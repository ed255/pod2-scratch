use itertools::Itertools;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::{hash_types::HashOut, poseidon::PoseidonHash};
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;
use std::fmt;
use std::io::{self, Write};
use strum_macros::FromRepr;

use crate::frontend;
use crate::F;

#[derive(Clone, Debug, Copy)]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
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
pub type Hash = Value;
pub type PodId = Hash;
pub const SELF: PodId = Value([F::ZERO; 4]);

impl From<&frontend::Value> for Value {
    fn from(v: &frontend::Value) -> Self {
        match v {
            frontend::Value::String(s) => hash_str(s),
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

impl From<frontend::Hash> for Hash {
    fn from(v: frontend::Hash) -> Self {
        Hash::default() // TODO
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v0 = self.0[0].to_canonical_u64();
        for i in 0..4 {
            write!(f, "{:02x}", (v0 >> (i * 8)) & 0xff)?;
        }
        Ok(())
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
            id: PodId::default(), // TODO
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
    pub input_signed_pods: Vec<Option<SignedPod>>,
    pub statements: Vec<Statement>,
}

impl MainPod {
    fn pad_statements(params: &Params, statements: &mut Vec<Statement>) {
        let mut args = Vec::new();
        Self::pad_statement_args(&params, &mut args);
        while statements.len() < params.max_statements {
            statements.push(Statement(NativeStatement::None, args.clone()));
        }
    }

    fn pad_statement_args(params: &Params, args: &mut Vec<StatementArg>) {
        while args.len() < params.max_statement_args {
            args.push(StatementArg::None);
        }
    }

    fn pad_input_signed_pods(params: &Params, pods: &mut Vec<Option<SignedPod>>) {
        while pods.len() < params.max_input_signed_pods {
            pods.push(None);
        }
    }

    pub fn compile(params: Params, pod: &frontend::MainPod) -> Self {
        let mut statements = Vec::new();
        let mut const_cnt = 0;
        for front_st in &pod.statements {
            let mut args = Vec::new();
            let frontend::Statement(front_typ, front_args) = front_st;
            for front_arg in front_args {
                let key = match front_arg {
                    frontend::StatementArg::Literal(v) => {
                        let key = format!("_c{}", const_cnt);
                        let key_hash = hash_str(&key);
                        const_cnt += 1;
                        let mut value_of_args = vec![
                            StatementArg::Ref(AnchoredKey(SELF, key_hash)),
                            StatementArg::Literal(Value::from(v)),
                        ];
                        Self::pad_statement_args(&params, &mut value_of_args);
                        statements.push(Statement(NativeStatement::ValueOf, value_of_args));
                        AnchoredKey(SELF, key_hash)
                    }
                    frontend::StatementArg::Ref(k) => {
                        AnchoredKey(PodId::from(k.0 .1 .0), hash_str(&k.1))
                    }
                };
                args.push(StatementArg::Ref(key));
                if args.len() > params.max_statement_args {
                    panic!("too many statement args");
                }
            }
            Self::pad_statement_args(&params, &mut args);
            statements.push(Statement(NativeStatement::from(*front_typ), args));
            if statements.len() > params.max_statements {
                panic!("too many statements");
            }
        }
        Self::pad_statements(&params, &mut statements);
        let mut input_signed_pods = pod
            .input_signed_pods
            .iter()
            .map(|p| Some(SignedPod::compile(params, p)))
            .collect();
        Self::pad_input_signed_pods(&params, &mut input_signed_pods);
        Self {
            params,
            id: PodId::default(), // TODO
            input_signed_pods,
            statements,
        }
    }
}

pub fn hash_str(s: &str) -> Hash {
    let mut input = s.as_bytes().to_vec();
    input.push(1); // padding
                   // Merge 7 bytes into 1 field, because the field is slightly below 64 bits
    let input: Vec<F> = input
        .chunks(7)
        .map(|bytes| {
            let mut v: u64 = 0;
            for b in bytes.iter().rev() {
                v <<= 8;
                v += *b as u64;
            }
            F::from_canonical_u64(v)
        })
        .collect();
    Value(PoseidonHash::hash_no_pad(&input).elements)
}

pub struct Printer {}

impl Printer {
    pub fn fmt_arg(&self, arg: &StatementArg, w: &mut dyn Write) -> io::Result<()> {
        match arg {
            StatementArg::None => write!(w, "none"),
            StatementArg::Literal(v) => write!(w, "{}", v),
            StatementArg::Ref(r) => write!(w, "{}.{}", r.0, r.1),
        }
    }

    pub fn fmt_signed_pod(&self, pod: &SignedPod, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w, "SignedPod ({}):", pod.id)?;
        // for (k, v) in pod.kvs.iter().sorted_by_key(|kv| kv.0) {
        // TODO: print in a stable order
        for (k, v) in pod.kvs.iter() {
            println!("  - {}: {}", k, v);
        }
        Ok(())
    }

    pub fn fmt_main_pod(&self, pod: &MainPod, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w, "MainPod ({}):", pod.id)?;
        writeln!(w, "  input_signed_pods:")?;
        for (i, in_pod) in pod.input_signed_pods.iter().enumerate() {
            if let Some(in_pod) = in_pod {
                writeln!(w, "    {:02}. {}", i, in_pod.id)?;
            } else {
                writeln!(w, "    {:02}. none", i)?;
            }
        }
        // TODO
        // writeln!(w, "  input_main_pods:")?;
        // for in_pod in &pod.input_main_pods {
        //     writeln!(w, "    - {}", in_pod.id)?;
        // }
        writeln!(w, "  prv statements:")?;
        for (i, st) in pod.statements.iter().enumerate() {
            if i == pod.params.max_statements - pod.params.max_public_statements {
                writeln!(w, "  pub statements:")?;
            }
            write!(w, "    {:03}. {:?} ", i, st.0)?;
            for (i, arg) in st.1.iter().enumerate() {
                if i != 0 {
                    write!(w, " ")?;
                }
                self.fmt_arg(arg, w)?;
            }
            write!(w, "\n")?;
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
        printer.fmt_signed_pod(&gov_id, &mut w).unwrap();
        printer.fmt_signed_pod(&pay_stub, &mut w).unwrap();
        printer.fmt_main_pod(&kyc, &mut w).unwrap();
    }
}
