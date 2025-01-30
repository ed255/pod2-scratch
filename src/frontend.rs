use hex::{FromHex, FromHexError};
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;
use std::io::{self, Write};

use crate::{hash_str, Hash, PodId, F, SELF};

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub enum PodType {
    #[default]
    Signed = 1,
    Main,
}

// An Origin, which represents a reference to an ancestor POD.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Origin(pub PodType, pub PodId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleTree {
    pub root: u8, // TODO
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    String(String),
    Int(i64),
    MerkleTree(MerkleTree),
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_string())
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::Int(v)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Int(v) => write!(f, "{}", v),
            Value::MerkleTree(mt) => write!(f, "mt:{}", mt.root),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignedPod {
    pub id: PodId,
    pub kvs: HashMap<String, Value>,
}

impl SignedPod {
    pub fn origin(&self) -> Origin {
        Origin(PodType::Signed, self.id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeStatement {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredKey(pub Origin, pub String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    Literal(Value),
    Ref(AnchoredKey),
}

impl From<Value> for StatementArg {
    fn from(v: Value) -> Self {
        StatementArg::Literal(v)
    }
}

impl From<&str> for StatementArg {
    fn from(s: &str) -> Self {
        StatementArg::Literal(Value::from(s))
    }
}

impl From<i64> for StatementArg {
    fn from(v: i64) -> Self {
        StatementArg::Literal(Value::from(v))
    }
}

impl From<(Origin, &str)> for StatementArg {
    fn from((origin, key): (Origin, &str)) -> Self {
        StatementArg::Ref(AnchoredKey(origin, key.to_string()))
    }
}

impl From<(&SignedPod, &str)> for StatementArg {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        StatementArg::Ref(AnchoredKey(pod.origin(), key.to_string()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub NativeStatement, pub Vec<StatementArg>);

#[derive(Clone, Debug)]
pub struct MainPodBuilder {
    pub statements: Vec<Statement>,
    pub operations: Vec<Operation>,
}

impl MainPodBuilder {
    pub fn push_statement(&mut self, st: Statement, op: Operation) {
        self.statements.push(st);
        self.operations.push(op);
    }
    pub fn build(self) -> MainPod {
        MainPod {
            id: PodId::default(),      // TODO
            input_signed_pods: vec![], // TODO
            input_main_pods: vec![],   // TODO
            statements: self
                .statements
                .into_iter()
                .zip(self.operations.into_iter())
                .collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MainPod {
    pub id: PodId,
    pub input_signed_pods: Vec<SignedPod>,
    pub input_main_pods: Vec<MainPod>,
    pub statements: Vec<(Statement, Operation)>,
}

impl MainPod {
    pub fn origin(&self) -> Origin {
        Origin(PodType::Main, self.id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeOperation {
    TransitiveEqualityFromStatements = 1,
    GtToNonequality = 2,
    LtToNonequality = 3,
    Auto = 1024,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationArg {
    Statement(Statement),
    Key(AnchoredKey),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation(pub NativeOperation, pub Vec<OperationArg>);

pub struct Printer {}

impl Printer {
    pub fn fmt_st_arg(&self, w: &mut dyn Write, arg: &StatementArg) -> io::Result<()> {
        match arg {
            StatementArg::Literal(v) => write!(w, "{}", v),
            StatementArg::Ref(r) => write!(w, "{}.{}", r.0 .1, r.1),
        }
    }

    pub fn fmt_st(&self, w: &mut dyn Write, st: &Statement) -> io::Result<()> {
        write!(w, "{:?} ", st.0)?;
        for (i, arg) in st.1.iter().enumerate() {
            if i != 0 {
                write!(w, " ")?;
            }
            self.fmt_st_arg(w, arg)?;
        }
        Ok(())
    }

    pub fn fmt_op_arg(&self, w: &mut dyn Write, arg: &OperationArg) -> io::Result<()> {
        match arg {
            OperationArg::Statement(s) => self.fmt_st(w, s),
            OperationArg::Key(r) => write!(w, "{}.{}", r.0 .1, r.1),
        }
    }

    pub fn fmt_op(&self, w: &mut dyn Write, op: &Operation) -> io::Result<()> {
        write!(w, "{:?} ", op.0)?;
        for (i, arg) in op.1.iter().enumerate() {
            if i != 0 {
                write!(w, " ")?;
            }
            self.fmt_op_arg(w, arg)?;
        }
        Ok(())
    }

    pub fn fmt_signed_pod(&self, w: &mut dyn Write, pod: &SignedPod) -> io::Result<()> {
        writeln!(w, "SignedPod (id:{}):", pod.id)?;
        for (k, v) in pod.kvs.iter().sorted_by_key(|kv| kv.0) {
            println!("  - {}: {}", k, v);
        }
        Ok(())
    }

    pub fn fmt_main_pod(&self, w: &mut dyn Write, pod: &MainPod) -> io::Result<()> {
        writeln!(w, "MainPod (id:{}):", pod.id)?;
        writeln!(w, "  input_signed_pods:")?;
        for in_pod in &pod.input_signed_pods {
            writeln!(w, "    - {}", in_pod.id)?;
        }
        writeln!(w, "  input_main_pods:")?;
        for in_pod in &pod.input_main_pods {
            writeln!(w, "    - {}", in_pod.id)?;
        }
        writeln!(w, "  statements:")?;
        for st in &pod.statements {
            let (st, op) = st;
            write!(w, "    - ")?;
            self.fmt_st(w, st)?;
            write!(w, " <- ",)?;
            self.fmt_op(w, op)?;
            write!(w, "\n")?;
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::io;

    fn pod_id(hex: &str) -> PodId {
        PodId(Hash::from_hex(hex).unwrap())
    }

    fn auto() -> Operation {
        Operation(NativeOperation::Auto, vec![])
    }

    macro_rules! args {
        ($($arg:expr),+) => {vec![$(StatementArg::from($arg)),*]}
    }

    macro_rules! st {
        (eq, $($arg:expr),+) => { Statement(NativeStatement::Equal, args!($($arg),*)) };
        (ne, $($arg:expr),+) => { Statement(NativeStatement::NotEqual, args!($($arg),*)) };
        (gt, $($arg:expr),+) => { Statement(NativeStatement::Gt, args!($($arg),*)) };
        (lt, $($arg:expr),+) => { Statement(NativeStatement::Lt, args!($($arg),*)) };
        (contains, $($arg:expr),+) => { Statement(NativeStatement::Contains, args!($($arg),*)) };
        (not_contains, $($arg:expr),+) => { Statement(NativeStatement::NotContains, args!($($arg),*)) };
        (sum_of, $($arg:expr),+) => { Statement(NativeStatement::SumOf, args!($($arg),*)) };
        (product_of, $($arg:expr),+) => { Statement(NativeStatement::product_of, args!($($arg),*)) };
        (max_of, $($arg:expr),+) => { Statement(NativeStatement::max_of, args!($($arg),*)) };
    }

    pub fn data_zu_kyc() -> (SignedPod, SignedPod, MainPod) {
        let mut kvs = HashMap::new();
        kvs.insert("idNumber".into(), "4242424242".into());
        kvs.insert("dateOfBirth".into(), 1169909384.into());
        kvs.insert("socialSecurityNumber".into(), "G2121210".into());
        let gov_id = SignedPod {
            id: pod_id("1100000000000000000000000000000000000000000000000000000000000000"),
            kvs,
        };

        let mut kvs = HashMap::new();
        kvs.insert("socialSecurityNumber".into(), "G2121210".into());
        kvs.insert("startDate".into(), 1706367566.into());
        let pay_stub = SignedPod {
            id: pod_id("2200000000000000000000000000000000000000000000000000000000000000"),
            kvs,
        };

        let sanction_list = Value::MerkleTree(MerkleTree { root: 1 });
        let now_minus_18y: i64 = 1169909388;
        let now_minus_1y: i64 = 1706367566;
        let mut statements: Vec<(Statement, Operation)> = Vec::new();
        statements.push((
            st!(not_contains, sanction_list, (&gov_id, "idNumber")),
            auto(),
        ));
        statements.push((st!(lt, (&gov_id, "dateOfBirth"), now_minus_18y), auto()));
        statements.push((
            st!(
                eq,
                (&gov_id, "socialSecurityNumber"),
                (&pay_stub, "socialSecurityNumber")
            ),
            auto(),
        ));
        statements.push((st!(eq, (&pay_stub, "startDate"), now_minus_1y), auto()));
        let kyc = MainPod {
            id: pod_id("3300000000000000000000000000000000000000000000000000000000000000"),
            input_signed_pods: vec![gov_id.clone(), pay_stub.clone()],
            input_main_pods: vec![],
            statements,
        };

        (gov_id, pay_stub, kyc)
    }

    #[test]
    fn test_front_0() {
        let (gov_id, pay_stub, kyc) = data_zu_kyc();

        let printer = Printer {};
        let mut w = io::stdout();
        printer.fmt_signed_pod(&mut w, &gov_id).unwrap();
        printer.fmt_signed_pod(&mut w, &pay_stub).unwrap();
        printer.fmt_main_pod(&mut w, &kyc).unwrap();
    }
}
