use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;

define_language! {
    pub enum LLL {
        Bool(bool),
        Num(i32),

        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "=" = Eq([Id; 2]),

        "app" = App([Id; 2]),
        "lll" = LLL([Id; 2]),
        "let" = Let([Id; 3]),
        "fix" = Fix([Id; 2]),

        "if" = If([Id; 3]),

        Symbol(egg::Symbol),
    }
}

impl LLL {
    fn num(&self) -> Option<i32> {
        match self {
            LLL::Num(n) => Some(*n),
            _ => None,
        }
    }
}

type EGraph = egg::EGraph<LLL, LLLAnalysis>;

#[derive(Default)]
pub struct LLLAnalysis;

#[derive(Debug)]
pub struct Data {
    free: HashSet<Id>,
    constant: Option<LLL>,
}

fn eval(egraph: &EGraph, enode: &LLL) -> Option<LLL> {
    let x = |i: &Id| egraph[*i].data.constant.clone();
    match enode {
        LLL::Num(_) => Some(enode.clone()),
        LLL::Add([a, b]) => Some(LLL::Num(x(a)?.num()? + x(b)?.num()?)),
        LLL::Eq([a, b]) => Some(LLL::Bool(x(a)? == x(b)?)),
        _ => None,
    }
}

impl Analysis<LLL> for LLLAnalysis {
    type Data = Data;

    fn merge(&self, to: &mut Data, from: Data) -> bool {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        let did_change = before_len != to.free.len();
        if to.constant.is_none() && from.constant.is_some() {
            to.constant = from.constant;
            true
        } else {
            did_change
        }
    }

    fn make(egraph: &EGraph, enode: &LLL) -> Data {
        let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        let mut free = HashSet::default();
        match enode {
            LLL::Var(v) => {
                free.insert(*v);
            }
            LLL::Let([v, a, b]) => {
                free.extend(f(b));
                free.remove(v);
                free.extend(f(a));
            }
            LLL::LLL([v, a]) | LLL::Fix([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            let const_id = egraph.add(c);
            egraph.union(id, const_id);
        }
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v]].data.constant.is_some()
}

pub fn rules() -> Vec<Rewrite<LLL, LLLAnalysis>> {
    vec![
        // open term rules
        rw!("if-true";   "(if  true ?then ?else)" => "?then"),
        rw!("if-false";  "(if false ?then ?else)" => "?else"),
        rw!("if-elim";   "(if (= (var ?x) ?e) ?then ?else)" => "?else"
            if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        // subst rules
        rw!("fix";       "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
        rw!("beta";      "(app (lll ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("let-app";   "(let ?v ?e (app ?a ?b))" => "(app (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-add";   "(let ?v ?e (+   ?a ?b))" => "(+   (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-eq";    "(let ?v ?e (=   ?a ?b))" => "(=   (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-const"; "(let ?v ?e ?c)" => "?c"
            if is_const(var("?c"))),
        rw!("let-if";
            "(let ?v ?e (if ?cond ?then ?else))" =>
            "(if (let ?v ?e ?cond) (let ?v ?e ?then) (let ?v ?e ?else))"
        ),
        rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-lll-same"; "(let ?v1 ?e (lll ?v1 ?body))" => "(lll ?v1 ?body)"),
        rw!("let-lll-diff";
            "(let ?v1 ?e (lll ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lll ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lll ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
    ]
}

struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<LLL>,
    if_free: Pattern<LLL>,
}

impl Applier<LLL, LLLAnalysis> for CaptureAvoid {
    fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = LLL::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free.apply_one(egraph, eclass, &subst)
        } else {
            self.if_not_free.apply_one(egraph, eclass, &subst)
        }
    }
}
