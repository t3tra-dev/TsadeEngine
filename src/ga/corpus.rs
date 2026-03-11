use crate::ga::{GAConfig, evolve_theorem};
use crate::kernel::{Ctx, FOTerm, Ty, tm_case_nodes, tm_repeat_case_nodes};
#[cfg(test)]
use crate::kernel::{find_kripke_countermodel, is_intuitionistic_theorem};

#[derive(Clone, Debug)]
pub struct TheoremCase {
    pub name: String,
    pub ctx: Ctx,
    pub target: Ty,
    pub expected_provable: bool,
}

#[derive(Clone, Debug)]
pub struct TheoremCaseCategory {
    pub name: &'static str,
    pub cases: Vec<TheoremCase>,
}

#[derive(Clone, Debug)]
pub struct TheoremStat {
    pub name: String,
    pub attempts: usize,
    pub solved: usize,
    pub expected_provable: bool,
    pub sample_proof: Option<String>,
    pub sample_case_nodes: Option<usize>,
    pub sample_repeat_case_nodes: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct CorpusReport {
    pub total_cases: usize,
    pub total_attempts: usize,
    pub total_solved: usize,
    pub true_positive: usize,
    pub true_negative: usize,
    pub false_positive: usize,
    pub false_negative: usize,
    pub avg_min_holes: f64,
    pub avg_min_goal_complexity: f64,
    pub avg_min_case_nodes: f64,
    pub avg_min_repeat_case_nodes: f64,
    pub avg_final_case_nodes: f64,
    pub avg_final_repeat_case_nodes: f64,
    pub avg_max_pair_nodes_seen: f64,
    pub avg_max_sum_intro_nodes_seen: f64,
    pub avg_max_proj_nodes_seen: f64,
    pub solved_with_case_ratio: f64,
    pub avg_memo_hits: f64,
    pub avg_dedup_dropped: f64,
    pub avg_repair_invocations: f64,
    pub avg_repair_goal_attempts: f64,
    pub avg_repair_candidates_tried: f64,
    pub avg_repair_success_steps: f64,
    pub avg_repair_promoted_states: f64,
    pub per_case: Vec<TheoremStat>,
}

#[derive(Clone, Debug)]
pub struct TrainTestReport {
    pub train: CorpusReport,
    pub test: CorpusReport,
}

impl CorpusReport {
    pub fn success_rate(&self) -> f64 {
        if self.total_attempts == 0 {
            return 0.0;
        }
        self.total_solved as f64 / self.total_attempts as f64
    }
}

fn theorem_case_with_ctx(
    name: &'static str,
    ctx: Vec<Ty>,
    target: Ty,
    expected_provable: bool,
) -> TheoremCase {
    TheoremCase {
        name: name.to_string(),
        ctx,
        target,
        expected_provable,
    }
}

fn prop_case(name: &'static str, target: Ty) -> TheoremCase {
    theorem_case_with_ctx(name, vec![], target, true)
}

fn prop_unprovable_case(name: &'static str, target: Ty) -> TheoremCase {
    theorem_case_with_ctx(name, vec![], target, false)
}

fn flatten_case_categories(categories: &[TheoremCaseCategory]) -> Vec<TheoremCase> {
    categories
        .iter()
        .flat_map(|category| category.cases.iter().cloned())
        .collect()
}

pub fn prop_implicational_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);

    vec![
        prop_case("I_identity", arr(a.clone(), a.clone())),
        prop_case("K_const", chain(vec![a.clone(), b.clone(), a.clone()])),
        prop_case(
            "S_apply",
            chain(vec![
                arr(a.clone(), arr(b.clone(), c.clone())),
                arr(a.clone(), b.clone()),
                a.clone(),
                c.clone(),
            ]),
        ),
        prop_case(
            "App",
            chain(vec![arr(a.clone(), b.clone()), a.clone(), b.clone()]),
        ),
        prop_case(
            "Comp",
            chain(vec![
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                a.clone(),
                c.clone(),
            ]),
        ),
        prop_case(
            "Flip",
            chain(vec![
                arr(a.clone(), arr(b.clone(), c.clone())),
                b.clone(),
                a.clone(),
                c.clone(),
            ]),
        ),
        prop_case(
            "W_diag",
            chain(vec![
                arr(a.clone(), arr(a.clone(), b.clone())),
                a.clone(),
                b.clone(),
            ]),
        ),
        prop_case(
            "B_comp",
            chain(vec![
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                arr(a.clone(), c.clone()),
            ]),
        ),
        prop_case(
            "Syllogism",
            chain(vec![
                arr(a.clone(), b.clone()),
                arr(b.clone(), c.clone()),
                arr(a.clone(), c.clone()),
            ]),
        ),
    ]
}

pub fn prop_currying_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);

    vec![
        prop_case(
            "Curry",
            chain(vec![
                arr(
                    Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                    c.clone(),
                ),
                a.clone(),
                b.clone(),
                c.clone(),
            ]),
        ),
        prop_case(
            "Uncurry",
            chain(vec![
                arr(a.clone(), arr(b.clone(), c.clone())),
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                c.clone(),
            ]),
        ),
    ]
}

pub fn prop_product_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    vec![
        prop_case(
            "Pair_intro",
            chain(vec![
                a.clone(),
                b.clone(),
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
            ]),
        ),
        prop_case(
            "Fst",
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                a.clone(),
            ),
        ),
        prop_case(
            "Snd",
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                b.clone(),
            ),
        ),
        prop_case(
            "Pair_comm",
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Prod(Box::new(b.clone()), Box::new(a.clone())),
            ),
        ),
        prop_case(
            "Pair_assoc",
            arr(
                Ty::Prod(
                    Box::new(a.clone()),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
        ),
        prop_case(
            "Pair_dup",
            arr(
                a.clone(),
                Ty::Prod(Box::new(a.clone()), Box::new(a.clone())),
            ),
        ),
        prop_case(
            "Pair_map",
            chain(vec![
                Ty::Prod(
                    Box::new(arr(a.clone(), b.clone())),
                    Box::new(arr(a.clone(), c.clone())),
                ),
                a.clone(),
                Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
            ]),
        ),
        prop_case(
            "Pair_unit_left",
            arr(
                Ty::Prod(Box::new(Ty::Atom(99)), Box::new(a.clone())),
                a.clone(),
            ),
        ),
        prop_case(
            "DeepProdNest",
            arr(
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(c.clone()), Box::new(d.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(d.clone()))),
                ),
            ),
        ),
    ]
}

pub fn prop_sum_basic_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);

    vec![
        prop_case(
            "Sum_inl",
            arr(a.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        ),
        prop_case(
            "Sum_inr",
            arr(b.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        ),
        prop_case(
            "Sum_elim",
            chain(vec![
                arr(a.clone(), c.clone()),
                arr(b.clone(), c.clone()),
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                c.clone(),
            ]),
        ),
        prop_case(
            "Sum_comm",
            arr(
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Sum(Box::new(b.clone()), Box::new(a.clone())),
            ),
        ),
        prop_case(
            "Sum_assoc",
            arr(
                Ty::Sum(
                    Box::new(a.clone()),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
        ),
        prop_case(
            "TripleNestedSum",
            arr(
                Ty::Sum(
                    Box::new(a.clone()),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
        ),
        prop_case(
            "SumSymmVariant",
            arr(
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(a.clone()))),
                    Box::new(c.clone()),
                ),
            ),
        ),
        prop_case(
            "Sum_bot_left",
            arr(Ty::Sum(Box::new(Ty::Bot), Box::new(a.clone())), a.clone()),
        ),
        prop_case(
            "Sum_bot_right",
            arr(Ty::Sum(Box::new(a.clone()), Box::new(Ty::Bot)), a.clone()),
        ),
    ]
}

pub fn prop_sum_distrib_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    vec![
        prop_case(
            "Sum_map",
            chain(vec![
                arr(a.clone(), c.clone()),
                arr(b.clone(), d.clone()),
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Sum(Box::new(c.clone()), Box::new(d.clone())),
            ]),
        ),
        prop_case(
            "SumMap2",
            chain(vec![
                arr(a.clone(), c.clone()),
                arr(b.clone(), d.clone()),
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Sum(Box::new(c.clone()), Box::new(d.clone())),
            ]),
        ),
        prop_case(
            "Sum_prod_distrib_left",
            arr(
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
                Ty::Sum(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
                ),
            ),
        ),
        prop_case(
            "Sum_prod_distrib_right",
            arr(
                Ty::Prod(
                    Box::new(a.clone()),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                ),
            ),
        ),
    ]
}

pub fn prop_negation_core_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    vec![
        prop_case("ExFalso", arr(Ty::Bot, a.clone())),
        prop_case(
            "Contradiction",
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
                Ty::Bot,
            ),
        ),
        prop_case(
            "Explosion",
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
                b.clone(),
            ),
        ),
        prop_case("DoubleNeg_intro", arr(a.clone(), neg(neg(a.clone())))),
        prop_case(
            "Contrapositive",
            chain(vec![
                arr(a.clone(), b.clone()),
                arr(neg(b.clone()), neg(a.clone())),
            ]),
        ),
        prop_case("TripleNeg", arr(neg(neg(neg(a.clone()))), neg(a.clone()))),
        prop_case(
            "NegationChain",
            chain(vec![
                arr(a.clone(), b.clone()),
                arr(b.clone(), c.clone()),
                arr(c.clone(), d.clone()),
                arr(neg(d.clone()), neg(a.clone())),
            ]),
        ),
    ]
}

pub fn prop_negation_demorgan_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);

    vec![
        prop_case(
            "DeMorgan_and_to_or",
            arr(
                Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
                neg(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
            ),
        ),
        prop_case(
            "DeMorgan_or_to_and",
            arr(
                neg(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            ),
        ),
        prop_case(
            "OrNeg_to_NegAnd",
            arr(
                Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
                neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
            ),
        ),
        prop_case(
            "WeakLEM",
            neg(neg(Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))))),
        ),
    ]
}

pub fn prop_unprovable_basic_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);

    vec![
        prop_unprovable_case("UNPROV_atom", a.clone()),
        prop_unprovable_case("UNPROV_impl", arr(a.clone(), b.clone())),
        prop_unprovable_case("UNPROV_bot", Ty::Bot),
    ]
}

pub fn prop_unprovable_classical_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);

    vec![
        prop_unprovable_case(
            "UNPROV_Peirce",
            arr(arr(arr(a.clone(), b.clone()), a.clone()), a.clone()),
        ),
        prop_unprovable_case("UNPROV_DNE", arr(neg(neg(a.clone())), a.clone())),
        prop_unprovable_case(
            "UNPROV_LEM",
            Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))),
        ),
        prop_unprovable_case(
            "UNPROV_NegAndToOr",
            arr(
                neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            ),
        ),
        prop_unprovable_case(
            "UNPROV_Dummett",
            Ty::Sum(
                Box::new(arr(a.clone(), b.clone())),
                Box::new(arr(b.clone(), a.clone())),
            ),
        ),
        prop_unprovable_case(
            "UNPROV_DeMorganReverse",
            arr(
                neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            ),
        ),
        prop_unprovable_case(
            "UNPROV_ContraReverse",
            chain(vec![
                arr(neg(a.clone()), neg(b.clone())),
                arr(b.clone(), a.clone()),
            ]),
        ),
    ]
}

pub fn prop_advanced_implicational_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);
    let e = Ty::Atom(4);
    let f = Ty::Atom(5);

    vec![
        prop_case(
            "HARD_LongChain",
            chain(vec![
                arr(d.clone(), e.clone()),
                arr(c.clone(), d.clone()),
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                a.clone(),
                e.clone(),
            ]),
        ),
        prop_case(
            "LongChain6",
            chain(vec![
                arr(e.clone(), f.clone()),
                arr(d.clone(), e.clone()),
                arr(c.clone(), d.clone()),
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                a.clone(),
                f.clone(),
            ]),
        ),
    ]
}

pub fn prop_advanced_mixed_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    vec![
        prop_case(
            "HARD_NestedSum",
            arr(
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Sum(Box::new(c.clone()), Box::new(d.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(d.clone()))),
                ),
            ),
        ),
        prop_case(
            "HARD_ContraProd",
            chain(vec![
                arr(
                    a.clone(),
                    Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
                ),
                arr(
                    Ty::Sum(Box::new(neg(b.clone())), Box::new(neg(c.clone()))),
                    neg(a.clone()),
                ),
            ]),
        ),
        prop_case(
            "HARD_MixedDistrib",
            arr(
                Ty::Sum(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(c.clone()), Box::new(d.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(d.clone()))),
                ),
            ),
        ),
        prop_case(
            "ComplexExplosion",
            arr(
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone())))),
                ),
                c.clone(),
            ),
        ),
    ]
}

pub fn propositional_case_categories() -> Vec<TheoremCaseCategory> {
    vec![
        TheoremCaseCategory {
            name: "prop-implicational",
            cases: prop_implicational_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-currying",
            cases: prop_currying_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-product",
            cases: prop_product_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-sum-basic",
            cases: prop_sum_basic_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-sum-distrib",
            cases: prop_sum_distrib_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-negation-core",
            cases: prop_negation_core_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-negation-demorgan",
            cases: prop_negation_demorgan_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-unprovable-basic",
            cases: prop_unprovable_basic_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-unprovable-classical",
            cases: prop_unprovable_classical_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-advanced-implicational",
            cases: prop_advanced_implicational_corpus(),
        },
        TheoremCaseCategory {
            name: "prop-advanced-mixed",
            cases: prop_advanced_mixed_corpus(),
        },
    ]
}

pub fn propositional_corpus() -> Vec<TheoremCase> {
    flatten_case_categories(&propositional_case_categories())
}

fn arr(a: Ty, b: Ty) -> Ty {
    Ty::Arr(Box::new(a), Box::new(b))
}

fn neg(a: Ty) -> Ty {
    arr(a, Ty::Bot)
}

fn chain(mut tys: Vec<Ty>) -> Ty {
    assert!(!tys.is_empty());
    let mut t = tys.pop().expect("non-empty");
    while let Some(h) = tys.pop() {
        t = Ty::Arr(Box::new(h), Box::new(t));
    }
    t
}

// ── Arithmetic corpus helpers ────────────────────────────────────────────────
// Signature:  0 = Const(0),  S = Func{sym:0},  + = Func{sym:1}

fn zero() -> FOTerm {
    FOTerm::Const(0)
}

fn succ(x: FOTerm) -> FOTerm {
    FOTerm::Func {
        sym: 0,
        args: vec![x],
    }
}

fn add(x: FOTerm, y: FOTerm) -> FOTerm {
    FOTerm::Func {
        sym: 1,
        args: vec![x, y],
    }
}

/// ∀x. x+0=x
fn ax_add_zero() -> Ty {
    Ty::Forall(Box::new(Ty::Eq(
        add(FOTerm::Var(0), zero()),
        FOTerm::Var(0),
    )))
}

/// ∀x∀y. x+S(y)=S(x+y)   (outer binder = x = Var(1), inner = y = Var(0))
fn ax_add_succ() -> Ty {
    Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Eq(
        add(FOTerm::Var(1), succ(FOTerm::Var(0))),
        succ(add(FOTerm::Var(1), FOTerm::Var(0))),
    )))))
}

fn arith_case(name: &'static str, ctx: Vec<Ty>, target: Ty) -> TheoremCase {
    theorem_case_with_ctx(name, ctx, target, true)
}

fn arith_unprovable_case(name: &'static str, ctx: Vec<Ty>, target: Ty) -> TheoremCase {
    theorem_case_with_ctx(name, ctx, target, false)
}

pub fn arith_equality_core_corpus() -> Vec<TheoremCase> {
    vec![
        arith_case(
            "A1_Refl",
            vec![],
            Ty::Forall(Box::new(Ty::Eq(FOTerm::Var(0), FOTerm::Var(0)))),
        ),
        arith_case(
            "A2_EqId",
            vec![],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Arr(
                Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
            ))))),
        ),
        arith_case(
            "A3_Symm",
            vec![],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Arr(
                Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                Box::new(Ty::Eq(FOTerm::Var(0), FOTerm::Var(1))),
            ))))),
        ),
        arith_case(
            "A4_Trans",
            vec![],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Forall(Box::new(
                Ty::Arr(
                    Box::new(Ty::Eq(FOTerm::Var(2), FOTerm::Var(1))),
                    Box::new(Ty::Arr(
                        Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                        Box::new(Ty::Eq(FOTerm::Var(2), FOTerm::Var(0))),
                    )),
                ),
            )))))),
        ),
        arith_case(
            "A5_CongS",
            vec![],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Arr(
                Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                Box::new(Ty::Eq(succ(FOTerm::Var(1)), succ(FOTerm::Var(0)))),
            ))))),
        ),
    ]
}

pub fn arith_equality_exists_corpus() -> Vec<TheoremCase> {
    vec![
        arith_case(
            "A6_ExistsYeqX",
            vec![],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Eq(
                FOTerm::Var(0),
                FOTerm::Var(1),
            ))))),
        ),
        arith_case(
            "A7_ExistsXeqY",
            vec![],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Eq(
                FOTerm::Var(1),
                FOTerm::Var(0),
            ))))),
        ),
        arith_case(
            "A8_SymmProd",
            vec![],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Arr(
                Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                Box::new(Ty::Prod(
                    Box::new(Ty::Eq(FOTerm::Var(1), FOTerm::Var(0))),
                    Box::new(Ty::Eq(FOTerm::Var(0), FOTerm::Var(1))),
                )),
            ))))),
        ),
    ]
}

pub fn arith_add_zero_core_corpus() -> Vec<TheoremCase> {
    vec![
        arith_case(
            "B1_AddZero",
            vec![ax_add_zero()],
            Ty::Forall(Box::new(Ty::Eq(
                add(FOTerm::Var(0), zero()),
                FOTerm::Var(0),
            ))),
        ),
        arith_case(
            "B4_GroundZero",
            vec![ax_add_zero()],
            Ty::Eq(add(zero(), zero()), zero()),
        ),
    ]
}

pub fn arith_add_zero_exists_corpus() -> Vec<TheoremCase> {
    vec![
        arith_case(
            "B2_ExistsAddZero",
            vec![ax_add_zero()],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Eq(
                add(FOTerm::Var(1), zero()),
                FOTerm::Var(0),
            ))))),
        ),
        arith_case(
            "B3_ExistsNeutral",
            vec![ax_add_zero()],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Eq(
                add(FOTerm::Var(1), FOTerm::Var(0)),
                FOTerm::Var(1),
            ))))),
        ),
        arith_case(
            "B5_ExistsProd",
            vec![ax_add_zero()],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Prod(
                Box::new(Ty::Eq(add(FOTerm::Var(1), zero()), FOTerm::Var(0))),
                Box::new(Ty::Eq(add(FOTerm::Var(0), zero()), FOTerm::Var(1))),
            ))))),
        ),
    ]
}

pub fn arith_add_succ_general_corpus() -> Vec<TheoremCase> {
    let s0 = succ(zero());

    vec![
        arith_case(
            "C1_AddSucc",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Eq(
                add(FOTerm::Var(1), succ(FOTerm::Var(0))),
                succ(add(FOTerm::Var(1), FOTerm::Var(0))),
            ))))),
        ),
        arith_case(
            "C2_AddOne",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Eq(
                add(FOTerm::Var(0), s0),
                succ(FOTerm::Var(0)),
            ))),
        ),
    ]
}

pub fn arith_add_succ_ground_corpus() -> Vec<TheoremCase> {
    let s0 = succ(zero());
    let s1 = succ(s0.clone());

    vec![
        arith_case(
            "C3_OnePlusOne",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Eq(add(s0.clone(), s0), s1),
        ),
        arith_case(
            "C4_ExistsAddOne",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Exists(Box::new(Ty::Eq(
                add(FOTerm::Var(1), succ(zero())),
                succ(FOTerm::Var(0)),
            ))))),
        ),
    ]
}

pub fn arith_induction_gap_corpus() -> Vec<TheoremCase> {
    vec![
        arith_unprovable_case(
            "U1_LeftUnit",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Eq(
                add(zero(), FOTerm::Var(0)),
                FOTerm::Var(0),
            ))),
        ),
        arith_unprovable_case(
            "U2_Comm",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Eq(
                add(FOTerm::Var(1), FOTerm::Var(0)),
                add(FOTerm::Var(0), FOTerm::Var(1)),
            ))))),
        ),
        arith_unprovable_case(
            "U3_Assoc",
            vec![ax_add_zero(), ax_add_succ()],
            Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Forall(Box::new(
                Ty::Eq(
                    add(add(FOTerm::Var(2), FOTerm::Var(1)), FOTerm::Var(0)),
                    add(FOTerm::Var(2), add(FOTerm::Var(1), FOTerm::Var(0))),
                ),
            )))))),
        ),
    ]
}

pub fn arithmetic_case_categories() -> Vec<TheoremCaseCategory> {
    vec![
        TheoremCaseCategory {
            name: "arith-equality-core",
            cases: arith_equality_core_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-equality-exists",
            cases: arith_equality_exists_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-add-zero-core",
            cases: arith_add_zero_core_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-add-zero-exists",
            cases: arith_add_zero_exists_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-add-succ-general",
            cases: arith_add_succ_general_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-add-succ-ground",
            cases: arith_add_succ_ground_corpus(),
        },
        TheoremCaseCategory {
            name: "arith-induction-gap",
            cases: arith_induction_gap_corpus(),
        },
    ]
}

/// Corpus covering FOL + equality + Robinson arithmetic (no induction).
pub fn arith_corpus() -> Vec<TheoremCase> {
    flatten_case_categories(&arithmetic_case_categories())
}

pub fn theorem_case_categories() -> Vec<TheoremCaseCategory> {
    let mut categories = propositional_case_categories();
    categories.extend(arithmetic_case_categories());
    categories
}

pub fn theorem_case_category(name: &str) -> Option<TheoremCaseCategory> {
    theorem_case_categories()
        .into_iter()
        .find(|category| category.name == name)
}

pub fn theorem_case_category_names() -> Vec<&'static str> {
    theorem_case_categories()
        .into_iter()
        .map(|category| category.name)
        .collect()
}

pub fn run_corpus(
    config: &GAConfig,
    seed: u64,
    repeats: usize,
    limit: Option<usize>,
) -> CorpusReport {
    let mut cases = propositional_corpus();
    if let Some(limit) = limit {
        cases.truncate(limit.min(cases.len()));
    }

    let mut per_case = Vec::new();
    let mut total_attempts = 0usize;
    let mut total_solved = 0usize;
    let mut tp = 0usize;
    let mut tn = 0usize;
    let mut fp = 0usize;
    let mut fn_ = 0usize;
    let mut sum_min_holes = 0usize;
    let mut sum_min_goal_complexity = 0usize;
    let mut sum_min_case_nodes = 0usize;
    let mut sum_min_repeat_case_nodes = 0usize;
    let mut sum_final_case_nodes = 0usize;
    let mut sum_final_repeat_case_nodes = 0usize;
    let mut sum_max_pair_nodes_seen = 0usize;
    let mut sum_max_sum_intro_nodes_seen = 0usize;
    let mut sum_max_proj_nodes_seen = 0usize;
    let mut solved_with_case = 0usize;
    let mut sum_memo_hits = 0usize;
    let mut sum_dedup_dropped = 0usize;
    let mut sum_repair_invocations = 0usize;
    let mut sum_repair_goal_attempts = 0usize;
    let mut sum_repair_candidates_tried = 0usize;
    let mut sum_repair_success_steps = 0usize;
    let mut sum_repair_promoted_states = 0usize;

    for (idx, case) in cases.iter().enumerate() {
        let mut solved = 0usize;
        let mut sample_proof: Option<String> = None;
        let mut sample_case_nodes: Option<usize> = None;
        let mut sample_repeat_case_nodes: Option<usize> = None;
        for r in 0..repeats.max(1) {
            total_attempts += 1;
            let run_seed = seed
                .wrapping_add((idx as u64).wrapping_mul(1_000_003))
                .wrapping_add((r as u64).wrapping_mul(9_973));
            let out = evolve_theorem(&case.ctx, &case.target, config, run_seed);
            sum_min_holes += out.best_metrics.min_holes;
            sum_min_goal_complexity += out.best_metrics.min_goal_complexity;
            sum_min_case_nodes += out.best_metrics.min_case_nodes;
            sum_min_repeat_case_nodes += out.best_metrics.min_repeat_case_nodes;
            sum_max_pair_nodes_seen += out.best_metrics.max_pair_nodes_seen;
            sum_max_sum_intro_nodes_seen += out.best_metrics.max_sum_intro_nodes_seen;
            sum_max_proj_nodes_seen += out.best_metrics.max_proj_nodes_seen;
            sum_memo_hits += out.best_metrics.memo_hits;
            sum_dedup_dropped += out.best_metrics.dedup_dropped;
            sum_repair_invocations += out.best_metrics.repair_invocations;
            sum_repair_goal_attempts += out.best_metrics.repair_goal_attempts;
            sum_repair_candidates_tried += out.best_metrics.repair_candidates_tried;
            sum_repair_success_steps += out.best_metrics.repair_success_steps;
            sum_repair_promoted_states += out.best_metrics.repair_promoted_states;
            if out.best_term.is_some() {
                solved += 1;
                total_solved += 1;
                if let Some(tm) = out.best_term.as_ref() {
                    let cn = tm_case_nodes(tm);
                    let rcn = tm_repeat_case_nodes(tm);
                    sum_final_case_nodes += cn;
                    sum_final_repeat_case_nodes += rcn;
                    if cn > 0 {
                        solved_with_case += 1;
                    }
                    if sample_case_nodes.is_none() {
                        sample_case_nodes = Some(cn);
                    }
                    if sample_repeat_case_nodes.is_none() {
                        sample_repeat_case_nodes = Some(rcn);
                    }
                }
                if sample_proof.is_none() {
                    sample_proof = out.best_term_pretty.clone();
                }
            }
        }

        if case.expected_provable {
            if solved > 0 {
                tp += 1;
            } else {
                fn_ += 1;
            }
        } else if solved > 0 {
            fp += 1;
        } else {
            tn += 1;
        }

        per_case.push(TheoremStat {
            name: case.name.clone(),
            attempts: repeats.max(1),
            solved,
            expected_provable: case.expected_provable,
            sample_proof,
            sample_case_nodes,
            sample_repeat_case_nodes,
        });
    }

    CorpusReport {
        total_cases: per_case.len(),
        total_attempts,
        total_solved,
        true_positive: tp,
        true_negative: tn,
        false_positive: fp,
        false_negative: fn_,
        avg_min_holes: sum_min_holes as f64 / total_attempts.max(1) as f64,
        avg_min_goal_complexity: sum_min_goal_complexity as f64 / total_attempts.max(1) as f64,
        avg_min_case_nodes: sum_min_case_nodes as f64 / total_attempts.max(1) as f64,
        avg_min_repeat_case_nodes: sum_min_repeat_case_nodes as f64 / total_attempts.max(1) as f64,
        avg_final_case_nodes: sum_final_case_nodes as f64 / total_solved.max(1) as f64,
        avg_final_repeat_case_nodes: sum_final_repeat_case_nodes as f64
            / total_solved.max(1) as f64,
        avg_max_pair_nodes_seen: sum_max_pair_nodes_seen as f64 / total_attempts.max(1) as f64,
        avg_max_sum_intro_nodes_seen: sum_max_sum_intro_nodes_seen as f64
            / total_attempts.max(1) as f64,
        avg_max_proj_nodes_seen: sum_max_proj_nodes_seen as f64 / total_attempts.max(1) as f64,
        solved_with_case_ratio: solved_with_case as f64 / total_solved.max(1) as f64,
        avg_memo_hits: sum_memo_hits as f64 / total_attempts.max(1) as f64,
        avg_dedup_dropped: sum_dedup_dropped as f64 / total_attempts.max(1) as f64,
        avg_repair_invocations: sum_repair_invocations as f64 / total_attempts.max(1) as f64,
        avg_repair_goal_attempts: sum_repair_goal_attempts as f64 / total_attempts.max(1) as f64,
        avg_repair_candidates_tried: sum_repair_candidates_tried as f64
            / total_attempts.max(1) as f64,
        avg_repair_success_steps: sum_repair_success_steps as f64 / total_attempts.max(1) as f64,
        avg_repair_promoted_states: sum_repair_promoted_states as f64
            / total_attempts.max(1) as f64,
        per_case,
    }
}

pub fn split_corpus(
    seed: u64,
    train_ratio_num: usize,
    train_ratio_den: usize,
    limit: Option<usize>,
) -> (Vec<TheoremCase>, Vec<TheoremCase>) {
    let mut cases = propositional_corpus();
    if let Some(limit) = limit {
        cases.truncate(limit.min(cases.len()));
    }
    let n = cases.len();
    if n <= 1 {
        return (cases, Vec::new());
    }

    // 軽量な決定的シャッフル (シード依存)
    let mut x = if seed == 0 { 0x9E3779B97F4A7C15 } else { seed };
    for i in (1..n).rev() {
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        let j = (x as usize) % (i + 1);
        cases.swap(i, j);
    }

    let den = train_ratio_den.max(1);
    let num = train_ratio_num.min(den);
    let mut train_size = n * num / den;
    if train_size == 0 {
        train_size = 1;
    }
    if train_size >= n {
        train_size = n - 1;
    }

    let test = cases.split_off(train_size);
    (cases, test)
}

pub fn run_train_test(
    config: &GAConfig,
    seed: u64,
    repeats: usize,
    train_ratio_num: usize,
    train_ratio_den: usize,
    limit: Option<usize>,
) -> TrainTestReport {
    let (train_cases, test_cases) = split_corpus(seed, train_ratio_num, train_ratio_den, limit);
    let train = run_corpus_on_cases(config, seed, repeats, &train_cases);
    let test = run_corpus_on_cases(
        config,
        seed.wrapping_add(1_000_000_007),
        repeats,
        &test_cases,
    );
    TrainTestReport { train, test }
}

pub fn run_corpus_cases(
    config: &GAConfig,
    seed: u64,
    repeats: usize,
    cases: &[TheoremCase],
) -> CorpusReport {
    run_corpus_on_cases(config, seed, repeats, cases)
}

fn run_corpus_on_cases(
    config: &GAConfig,
    seed: u64,
    repeats: usize,
    cases: &[TheoremCase],
) -> CorpusReport {
    let mut per_case = Vec::new();
    let mut total_attempts = 0usize;
    let mut total_solved = 0usize;
    let mut tp = 0usize;
    let mut tn = 0usize;
    let mut fp = 0usize;
    let mut fn_ = 0usize;
    let mut sum_min_holes = 0usize;
    let mut sum_min_goal_complexity = 0usize;
    let mut sum_min_case_nodes = 0usize;
    let mut sum_min_repeat_case_nodes = 0usize;
    let mut sum_final_case_nodes = 0usize;
    let mut sum_final_repeat_case_nodes = 0usize;
    let mut sum_max_pair_nodes_seen = 0usize;
    let mut sum_max_sum_intro_nodes_seen = 0usize;
    let mut sum_max_proj_nodes_seen = 0usize;
    let mut solved_with_case = 0usize;
    let mut sum_memo_hits = 0usize;
    let mut sum_dedup_dropped = 0usize;
    let mut sum_repair_invocations = 0usize;
    let mut sum_repair_goal_attempts = 0usize;
    let mut sum_repair_candidates_tried = 0usize;
    let mut sum_repair_success_steps = 0usize;
    let mut sum_repair_promoted_states = 0usize;

    for (idx, case) in cases.iter().enumerate() {
        let mut solved = 0usize;
        let mut sample_proof: Option<String> = None;
        let mut sample_case_nodes: Option<usize> = None;
        let mut sample_repeat_case_nodes: Option<usize> = None;
        for r in 0..repeats.max(1) {
            total_attempts += 1;
            let run_seed = seed
                .wrapping_add((idx as u64).wrapping_mul(1_000_003))
                .wrapping_add((r as u64).wrapping_mul(9_973));
            let out = evolve_theorem(&case.ctx, &case.target, config, run_seed);
            sum_min_holes += out.best_metrics.min_holes;
            sum_min_goal_complexity += out.best_metrics.min_goal_complexity;
            sum_min_case_nodes += out.best_metrics.min_case_nodes;
            sum_min_repeat_case_nodes += out.best_metrics.min_repeat_case_nodes;
            sum_max_pair_nodes_seen += out.best_metrics.max_pair_nodes_seen;
            sum_max_sum_intro_nodes_seen += out.best_metrics.max_sum_intro_nodes_seen;
            sum_max_proj_nodes_seen += out.best_metrics.max_proj_nodes_seen;
            sum_memo_hits += out.best_metrics.memo_hits;
            sum_dedup_dropped += out.best_metrics.dedup_dropped;
            sum_repair_invocations += out.best_metrics.repair_invocations;
            sum_repair_goal_attempts += out.best_metrics.repair_goal_attempts;
            sum_repair_candidates_tried += out.best_metrics.repair_candidates_tried;
            sum_repair_success_steps += out.best_metrics.repair_success_steps;
            sum_repair_promoted_states += out.best_metrics.repair_promoted_states;
            if out.best_term.is_some() {
                solved += 1;
                total_solved += 1;
                if let Some(tm) = out.best_term.as_ref() {
                    let cn = tm_case_nodes(tm);
                    let rcn = tm_repeat_case_nodes(tm);
                    sum_final_case_nodes += cn;
                    sum_final_repeat_case_nodes += rcn;
                    if cn > 0 {
                        solved_with_case += 1;
                    }
                    if sample_case_nodes.is_none() {
                        sample_case_nodes = Some(cn);
                    }
                    if sample_repeat_case_nodes.is_none() {
                        sample_repeat_case_nodes = Some(rcn);
                    }
                }
                if sample_proof.is_none() {
                    sample_proof = out.best_term_pretty.clone();
                }
            }
        }

        if case.expected_provable {
            if solved > 0 {
                tp += 1;
            } else {
                fn_ += 1;
            }
        } else if solved > 0 {
            fp += 1;
        } else {
            tn += 1;
        }

        per_case.push(TheoremStat {
            name: case.name.clone(),
            attempts: repeats.max(1),
            solved,
            expected_provable: case.expected_provable,
            sample_proof,
            sample_case_nodes,
            sample_repeat_case_nodes,
        });
    }

    CorpusReport {
        total_cases: per_case.len(),
        total_attempts,
        total_solved,
        true_positive: tp,
        true_negative: tn,
        false_positive: fp,
        false_negative: fn_,
        avg_min_holes: sum_min_holes as f64 / total_attempts.max(1) as f64,
        avg_min_goal_complexity: sum_min_goal_complexity as f64 / total_attempts.max(1) as f64,
        avg_min_case_nodes: sum_min_case_nodes as f64 / total_attempts.max(1) as f64,
        avg_min_repeat_case_nodes: sum_min_repeat_case_nodes as f64 / total_attempts.max(1) as f64,
        avg_final_case_nodes: sum_final_case_nodes as f64 / total_solved.max(1) as f64,
        avg_final_repeat_case_nodes: sum_final_repeat_case_nodes as f64
            / total_solved.max(1) as f64,
        avg_max_pair_nodes_seen: sum_max_pair_nodes_seen as f64 / total_attempts.max(1) as f64,
        avg_max_sum_intro_nodes_seen: sum_max_sum_intro_nodes_seen as f64
            / total_attempts.max(1) as f64,
        avg_max_proj_nodes_seen: sum_max_proj_nodes_seen as f64 / total_attempts.max(1) as f64,
        solved_with_case_ratio: solved_with_case as f64 / total_solved.max(1) as f64,
        avg_memo_hits: sum_memo_hits as f64 / total_attempts.max(1) as f64,
        avg_dedup_dropped: sum_dedup_dropped as f64 / total_attempts.max(1) as f64,
        avg_repair_invocations: sum_repair_invocations as f64 / total_attempts.max(1) as f64,
        avg_repair_goal_attempts: sum_repair_goal_attempts as f64 / total_attempts.max(1) as f64,
        avg_repair_candidates_tried: sum_repair_candidates_tried as f64
            / total_attempts.max(1) as f64,
        avg_repair_success_steps: sum_repair_success_steps as f64 / total_attempts.max(1) as f64,
        avg_repair_promoted_states: sum_repair_promoted_states as f64
            / total_attempts.max(1) as f64,
        per_case,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn corpus_labels_are_machine_checked() {
        let cases = propositional_corpus();
        for c in &cases {
            let decided = is_intuitionistic_theorem(&c.ctx, &c.target);
            assert_eq!(
                decided, c.expected_provable,
                "label mismatch: {} expected={} decided={}",
                c.name, c.expected_provable, decided
            );
        }
    }

    #[test]
    fn impossible_cases_are_not_theorems() {
        for c in propositional_corpus()
            .into_iter()
            .filter(|x| x.name.starts_with("IMPOSSIBLE_"))
        {
            assert!(!is_intuitionistic_theorem(&c.ctx, &c.target), "{}", c.name);
        }
    }

    #[test]
    fn impossible_cases_have_small_kripke_countermodels() {
        for c in propositional_corpus()
            .into_iter()
            .filter(|x| x.name.starts_with("IMPOSSIBLE_"))
        {
            let cm = find_kripke_countermodel(&c.ctx, &c.target, 4);
            assert!(cm.is_some(), "{}", c.name);
        }
    }

    #[test]
    fn arith_corpus_labels_are_machine_checked() {
        let cases = arith_corpus();
        for c in &cases {
            let decided = is_intuitionistic_theorem(&c.ctx, &c.target);
            assert_eq!(
                decided, c.expected_provable,
                "label mismatch: {} expected={} decided={}",
                c.name, c.expected_provable, decided
            );
        }
    }

    #[test]
    fn theorem_case_categories_have_expected_names() {
        let names = theorem_case_category_names();
        assert_eq!(
            names,
            vec![
                "prop-implicational",
                "prop-currying",
                "prop-product",
                "prop-sum-basic",
                "prop-sum-distrib",
                "prop-negation-core",
                "prop-negation-demorgan",
                "prop-unprovable-basic",
                "prop-unprovable-classical",
                "prop-advanced-implicational",
                "prop-advanced-mixed",
                "arith-equality-core",
                "arith-equality-exists",
                "arith-add-zero-core",
                "arith-add-zero-exists",
                "arith-add-succ-general",
                "arith-add-succ-ground",
                "arith-induction-gap",
            ]
        );
    }

    #[test]
    fn theorem_case_category_lookup_works() {
        let arith = theorem_case_category("arith-add-succ-ground")
            .expect("arith-add-succ-ground category exists");
        assert!(arith.cases.iter().any(|c| c.name == "C3_OnePlusOne"));
    }

    #[test]
    fn theorem_case_categories_are_disjoint() {
        let mut seen = std::collections::BTreeMap::new();
        for category in theorem_case_categories() {
            for case in category.cases {
                let prev = seen.insert(case.name.clone(), category.name);
                assert!(
                    prev.is_none(),
                    "case {} appears in both {} and {}",
                    case.name,
                    prev.unwrap_or(""),
                    category.name
                );
            }
        }
    }

    #[test]
    fn aggregate_corpora_match_category_unions() {
        let prop_from_categories: Vec<_> =
            flatten_case_categories(&propositional_case_categories())
                .into_iter()
                .map(|case| case.name)
                .collect();
        let prop_direct: Vec<_> = propositional_corpus()
            .into_iter()
            .map(|case| case.name)
            .collect();
        assert_eq!(prop_from_categories, prop_direct);

        let arith_from_categories: Vec<_> = flatten_case_categories(&arithmetic_case_categories())
            .into_iter()
            .map(|case| case.name)
            .collect();
        let arith_direct: Vec<_> = arith_corpus().into_iter().map(|case| case.name).collect();
        assert_eq!(arith_from_categories, arith_direct);
    }

    #[test]
    fn theorem_case_categories_labels_are_machine_checked() {
        for category in theorem_case_categories() {
            for c in &category.cases {
                let decided = is_intuitionistic_theorem(&c.ctx, &c.target);
                assert_eq!(
                    decided, c.expected_provable,
                    "label mismatch in category {}: {} expected={} decided={}",
                    category.name, c.name, c.expected_provable, decided
                );
            }
        }
    }
}
