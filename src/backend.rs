use itertools::Itertools;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::{hash_types::HashOut, poseidon::PoseidonHash};
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;
use std::fmt;
use std::io::{self, Write};
use std::iter;
use strum_macros::FromRepr;

use crate::frontend;
use crate::{hash_str, Hash, PodId, F, SELF};

#[derive(Clone, Debug, Copy)]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
}

impl Params {
    pub fn max_priv_statements(&self) -> usize {
        self.max_statements - self.max_public_statements
    }
}

impl Default for Params {
    fn default() -> Self {
        Self {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 20,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 5,
        }
    }
}

#[derive(Clone, Copy, Debug, FromRepr, PartialEq, Eq)]
pub enum NativeStatement {
    None = 0,
    ValueOf = 1,
    Equal = 2,
    NotEqual,
    Gt,
    Lt,
    Contains,
    NotContains,
    SumOf,
    ProductOf,
    MaxOf,
}

impl From<frontend::NativeStatement> for NativeStatement {
    fn from(v: frontend::NativeStatement) -> Self {
        Self::from_repr(v as usize).unwrap()
    }
}

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct Value(pub [F; 4]);

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0[2].is_zero() && self.0[3].is_zero() {
            // Assume this is an integer
            let (l0, l1) = (self.0[0].to_canonical_u64(), self.0[1].to_canonical_u64());
            assert!(l0 < (1 << 32));
            assert!(l1 < (1 << 32));
            write!(f, "{}", l0 + l1 * (1 << 32))
        } else {
            // Assume this is a hash
            Hash(self.0).fmt(f)
        }
    }
}

impl From<&frontend::Value> for Value {
    fn from(v: &frontend::Value) -> Self {
        match v {
            frontend::Value::String(s) => Self(hash_str(s).0),
            frontend::Value::Int(v) => {
                Value([F::from_canonical_u64(*v as u64), F::ZERO, F::ZERO, F::ZERO])
            }
            // TODO
            frontend::Value::MerkleTree(mt) => Value([
                F::from_canonical_u64(mt.root as u64),
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ]),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredKey(pub PodId, pub Hash);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    None,
    Literal(Value),
    Ref(AnchoredKey),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub NativeStatement, pub Vec<StatementArg>);

#[derive(Clone, Debug)]
pub struct SignedPod {
    pub params: Params,
    pub id: PodId,
    pub kvs: HashMap<Hash, Value>,
}

impl SignedPod {
    pub fn compile(params: Params, pod: &frontend::SignedPod) -> Self {
        Self {
            params,
            id: pod.id,
            kvs: pod
                .kvs
                .iter()
                .map(|(k, v)| (hash_str(k), Value::from(v)))
                .collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MainPod {
    pub params: Params,
    pub id: PodId,
    pub input_signed_pods: Vec<SignedPod>,
    pub statements: Vec<Statement>,
}

fn fill_pad<T: Clone>(v: &mut Vec<T>, pad_value: T, len: usize) {
    if v.len() > len {
        panic!("length exceeded");
    }
    while v.len() < len {
        v.push(pad_value.clone());
    }
}

impl MainPod {
    fn statement_none(params: &Params) -> Statement {
        let mut args = Vec::with_capacity(params.max_statement_args);
        Self::pad_statement_args(&params, &mut args);
        Statement(NativeStatement::None, args)
    }

    fn pad_statements(params: &Params, statements: &mut Vec<Statement>, len: usize) {
        for st in statements.iter_mut() {
            fill_pad(&mut st.1, StatementArg::None, params.max_statement_args)
        }
        fill_pad(statements, Self::statement_none(params), len)
    }

    fn pad_statement_args(params: &Params, args: &mut Vec<StatementArg>) {
        fill_pad(args, StatementArg::None, params.max_statement_args)
    }

    fn pad_input_signed_pods(params: &Params, pods: &mut Vec<SignedPod>) {
        let pod_none = SignedPod {
            params: params.clone(),
            id: PodId::default(),
            kvs: HashMap::new(),
        };
        fill_pad(pods, pod_none, params.max_input_signed_pods)
    }

    pub fn compile(params: Params, pod: &frontend::MainPod) -> Self {
        let mut statements = Vec::new();
        let mut const_cnt = 0;
        for front_st in &pod.statements {
            let mut args = Vec::new();
            let frontend::Statement(front_typ, front_args) = &front_st.0;
            for front_arg in front_args {
                let key = match front_arg {
                    frontend::StatementArg::Literal(v) => {
                        let key = format!("_c{}", const_cnt);
                        let key_hash = hash_str(&key);
                        const_cnt += 1;
                        let value_of_args = vec![
                            StatementArg::Ref(AnchoredKey(SELF, key_hash)),
                            StatementArg::Literal(Value::from(v)),
                        ];
                        statements.push(Statement(NativeStatement::ValueOf, value_of_args));
                        AnchoredKey(SELF, key_hash)
                    }
                    frontend::StatementArg::Ref(k) => AnchoredKey(k.0 .1, hash_str(&k.1)),
                };
                args.push(StatementArg::Ref(key));
                if args.len() > params.max_statement_args {
                    panic!("too many statement args");
                }
            }
            statements.push(Statement(NativeStatement::from(*front_typ), args));
            if statements.len() > params.max_statements {
                panic!("too many statements");
            }
        }
        Self::pad_statements(&params, &mut statements, params.max_statements);
        let mut input_signed_pods = pod
            .input_signed_pods
            .iter()
            .map(|p| SignedPod::compile(params, p))
            .collect();
        Self::pad_input_signed_pods(&params, &mut input_signed_pods);
        Self {
            params,
            id: PodId::default(), // TODO
            input_signed_pods,
            statements,
        }
    }

    pub fn max_priv_statements(&self) -> usize {
        self.params.max_statements - self.params.max_public_statements
    }

    pub fn input_signed_pods_statements(&self) -> Vec<Vec<Statement>> {
        let mut pods_statements = Vec::new();
        let st_none = Self::statement_none(&self.params);
        for pod in &self.input_signed_pods {
            let mut pod_statements: Vec<Statement> = Vec::new();
            for kv in &pod.kvs {
                let args = vec![
                    StatementArg::Ref(AnchoredKey(pod.id, *kv.0)),
                    StatementArg::Literal(*kv.1),
                ];
                pod_statements.push(Statement(NativeStatement::ValueOf, args));
            }
            Self::pad_statements(
                &self.params,
                &mut pod_statements,
                self.params.max_signed_pod_values,
            );
            pods_statements.push(pod_statements);
        }
        let statements_none: Vec<Statement> = iter::repeat(st_none.clone())
            .take(self.params.max_signed_pod_values)
            .collect();
        fill_pad(
            &mut pods_statements,
            statements_none,
            self.params.max_input_signed_pods,
        );
        pods_statements
    }

    pub fn prv_statements(&self) -> Vec<Statement> {
        self.statements
            .iter()
            .take(self.params.max_priv_statements())
            .cloned()
            .collect()
    }

    pub fn pub_statements(&self) -> Vec<Statement> {
        self.statements
            .iter()
            .skip(self.params.max_priv_statements())
            .cloned()
            .collect()
    }
}

pub struct Printer {}

impl Printer {
    pub fn fmt_arg(&self, w: &mut dyn Write, arg: &StatementArg) -> io::Result<()> {
        match arg {
            StatementArg::None => write!(w, "none"),
            StatementArg::Literal(v) => write!(w, "{}", v),
            StatementArg::Ref(r) => write!(w, "{}.{}", r.0, r.1),
        }
    }

    pub fn fmt_signed_pod(&self, w: &mut dyn Write, pod: &SignedPod) -> io::Result<()> {
        writeln!(w, "SignedPod ({}):", pod.id)?;
        // for (k, v) in pod.kvs.iter().sorted_by_key(|kv| kv.0) {
        // TODO: print in a stable order
        for (k, v) in pod.kvs.iter() {
            println!("  - {}: {}", k, v);
        }
        Ok(())
    }

    pub fn fmt_statement(&self, w: &mut dyn Write, st: &Statement) -> io::Result<()> {
        write!(w, "{:?} ", st.0)?;
        for (i, arg) in st.1.iter().enumerate() {
            if i != 0 {
                write!(w, " ")?;
            }
            self.fmt_arg(w, arg)?;
        }
        Ok(())
    }

    pub fn fmt_statement_index(
        &self,
        w: &mut dyn Write,
        st: &Statement,
        index: usize,
    ) -> io::Result<()> {
        write!(w, "    {:03}. ", index)?;
        self.fmt_statement(w, &st)?;
        write!(w, "\n")
    }

    pub fn fmt_main_pod(&self, w: &mut dyn Write, pod: &MainPod) -> io::Result<()> {
        writeln!(w, "MainPod ({}):", pod.id)?;
        // TODO
        // writeln!(w, "  input_main_pods:")?;
        // for in_pod in &pod.input_main_pods {
        //     writeln!(w, "    - {}", in_pod.id)?;
        // }
        let mut st_index = 0;
        for (i, (pod, statements)) in pod
            .input_signed_pods
            .iter()
            .zip(pod.input_signed_pods_statements())
            .enumerate()
        {
            writeln!(w, "  in sig_pod {:02} (id:{}) statements:", i, pod.id)?;
            for st in statements {
                self.fmt_statement_index(w, &st, st_index)?;
                st_index += 1;
            }
        }
        writeln!(w, "  prv statements:")?;
        for st in pod.prv_statements() {
            self.fmt_statement_index(w, &st, st_index)?;
            st_index += 1;
        }
        writeln!(w, "  pub statements:")?;
        for st in pod.pub_statements() {
            self.fmt_statement_index(w, &st, st_index)?;
            st_index += 1;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;

    #[test]
    fn test_back_0() {
        let params = Params::default();
        let (front_gov_id, front_pay_stub, front_kyc) = frontend::tests::data_zu_kyc();
        let gov_id = SignedPod::compile(params, &front_gov_id);
        let pay_stub = SignedPod::compile(params, &front_pay_stub);
        let kyc = MainPod::compile(params, &front_kyc);
        // println!("{:#?}", kyc);

        let printer = Printer {};
        let mut w = io::stdout();
        printer.fmt_signed_pod(&mut w, &gov_id).unwrap();
        printer.fmt_signed_pod(&mut w, &pay_stub).unwrap();
        printer.fmt_main_pod(&mut w, &kyc).unwrap();
    }
}
