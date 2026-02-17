use crate::ga::{GAConfig, evolve_theorem};
use crate::kernel::{Ctx, Ty, tm_case_nodes, tm_repeat_case_nodes};
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

pub fn implication_corpus() -> Vec<TheoremCase> {
    let mut out = Vec::new();
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    // === 基本定理 (10個) ===

    // 恒等関数
    out.push(TheoremCase {
        name: "I_identity".to_string(),
        ctx: vec![],
        target: arr(a.clone(), a.clone()),
        expected_provable: true,
    });

    // K combinator (定数関数)
    out.push(TheoremCase {
        name: "K_const".to_string(),
        ctx: vec![],
        target: chain(vec![a.clone(), b.clone(), a.clone()]),
        expected_provable: true,
    });

    // S combinator (関数適用)
    out.push(TheoremCase {
        name: "S_apply".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), arr(b.clone(), c.clone())),
            arr(a.clone(), b.clone()),
            a.clone(),
            c.clone(),
        ]),
        expected_provable: true,
    });

    // 関数適用
    out.push(TheoremCase {
        name: "App".to_string(),
        ctx: vec![],
        target: chain(vec![arr(a.clone(), b.clone()), a.clone(), b.clone()]),
        expected_provable: true,
    });

    // 関数合成
    out.push(TheoremCase {
        name: "Comp".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(b.clone(), c.clone()),
            arr(a.clone(), b.clone()),
            a.clone(),
            c.clone(),
        ]),
        expected_provable: true,
    });

    // Flip (引数の順序交換)
    out.push(TheoremCase {
        name: "Flip".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), arr(b.clone(), c.clone())),
            b.clone(),
            a.clone(),
            c.clone(),
        ]),
        expected_provable: true,
    });

    // カリー化
    out.push(TheoremCase {
        name: "Curry".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                c.clone(),
            ),
            a.clone(),
            b.clone(),
            c.clone(),
        ]),
        expected_provable: true,
    });

    // 非カリー化
    out.push(TheoremCase {
        name: "Uncurry".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), arr(b.clone(), c.clone())),
            Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
            c.clone(),
        ]),
        expected_provable: true,
    });

    // W combinator (対角化)
    out.push(TheoremCase {
        name: "W_diag".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), arr(a.clone(), b.clone())),
            a.clone(),
            b.clone(),
        ]),
        expected_provable: true,
    });

    // B combinator (合成の別形)
    out.push(TheoremCase {
        name: "B_comp".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(b.clone(), c.clone()),
            arr(a.clone(), b.clone()),
            arr(a.clone(), c.clone()),
        ]),
        expected_provable: true,
    });

    // === 直積 (Product) の定理 (8個) ===

    out.push(TheoremCase {
        name: "Pair_intro".to_string(),
        ctx: vec![],
        target: chain(vec![
            a.clone(),
            b.clone(),
            Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Fst".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
            a.clone(),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Snd".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
            b.clone(),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Pair_comm".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
            Ty::Prod(Box::new(b.clone()), Box::new(a.clone())),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Pair_assoc".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(
                Box::new(a.clone()),
                Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
            ),
            Ty::Prod(
                Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(c.clone()),
            ),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Pair_dup".to_string(),
        ctx: vec![],
        target: arr(
            a.clone(),
            Ty::Prod(Box::new(a.clone()), Box::new(a.clone())),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Pair_map".to_string(),
        ctx: vec![],
        target: chain(vec![
            Ty::Prod(
                Box::new(arr(a.clone(), b.clone())),
                Box::new(arr(a.clone(), c.clone())),
            ),
            a.clone(),
            Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Pair_unit_left".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(Ty::Atom(99)), Box::new(a.clone())),
            a.clone(),
        ),
        expected_provable: true,
    });

    // === 直和 (Sum) の定理 (10個) ===

    out.push(TheoremCase {
        name: "Sum_inl".to_string(),
        ctx: vec![],
        target: arr(a.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_inr".to_string(),
        ctx: vec![],
        target: arr(b.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_elim".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), c.clone()),
            arr(b.clone(), c.clone()),
            Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
            c.clone(),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_comm".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
            Ty::Sum(Box::new(b.clone()), Box::new(a.clone())),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_assoc".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Sum(
                Box::new(a.clone()),
                Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
            ),
            Ty::Sum(
                Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(c.clone()),
            ),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_map".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), c.clone()),
            arr(b.clone(), d.clone()),
            Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
            Ty::Sum(Box::new(c.clone()), Box::new(d.clone())),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_prod_distrib_left".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(
                Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(c.clone()),
            ),
            Ty::Sum(
                Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
            ),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_prod_distrib_right".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(
                Box::new(a.clone()),
                Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
            ),
            Ty::Sum(
                Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
            ),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_bot_left".to_string(),
        ctx: vec![],
        target: arr(Ty::Sum(Box::new(Ty::Bot), Box::new(a.clone())), a.clone()),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Sum_bot_right".to_string(),
        ctx: vec![],
        target: arr(Ty::Sum(Box::new(a.clone()), Box::new(Ty::Bot)), a.clone()),
        expected_provable: true,
    });

    // === 否定と矛盾 (Negation & Bot) の定理 (10個) ===

    out.push(TheoremCase {
        name: "ExFalso".to_string(),
        ctx: vec![],
        target: arr(Ty::Bot, a.clone()),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Contradiction".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
            Ty::Bot,
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Explosion".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
            b.clone(),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "DoubleNeg_intro".to_string(),
        ctx: vec![],
        target: arr(a.clone(), neg(neg(a.clone()))),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "Contrapositive".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(a.clone(), b.clone()),
            arr(neg(b.clone()), neg(a.clone())),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "TripleNeg".to_string(),
        ctx: vec![],
        target: arr(neg(neg(neg(a.clone()))), neg(a.clone())),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "DeMorgan_and_to_or".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            neg(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "DeMorgan_or_to_and".to_string(),
        ctx: vec![],
        target: arr(
            neg(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
            Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "OrNeg_to_NegAnd".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "WeakLEM".to_string(),
        ctx: vec![],
        target: neg(neg(Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))))),
        expected_provable: true,
    });

    // === 証明不可能な定理 (8個) ===

    out.push(TheoremCase {
        name: "UNPROV_atom".to_string(),
        ctx: vec![],
        target: a.clone(),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_impl".to_string(),
        ctx: vec![],
        target: arr(a.clone(), b.clone()),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_bot".to_string(),
        ctx: vec![],
        target: Ty::Bot,
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_Peirce".to_string(),
        ctx: vec![],
        target: arr(arr(arr(a.clone(), b.clone()), a.clone()), a.clone()),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_DNE".to_string(),
        ctx: vec![],
        target: arr(neg(neg(a.clone())), a.clone()),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_LEM".to_string(),
        ctx: vec![],
        target: Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_NegAndToOr".to_string(),
        ctx: vec![],
        target: arr(
            neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
            Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
        ),
        expected_provable: false,
    });

    out.push(TheoremCase {
        name: "UNPROV_Dummett".to_string(),
        ctx: vec![],
        target: Ty::Sum(
            Box::new(arr(a.clone(), b.clone())),
            Box::new(arr(b.clone(), a.clone())),
        ),
        expected_provable: false,
    });

    // === より難しい定理 (4個) ===

    out.push(TheoremCase {
        name: "HARD_LongChain".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(d.clone(), Ty::Atom(4)),
            arr(c.clone(), d.clone()),
            arr(b.clone(), c.clone()),
            arr(a.clone(), b.clone()),
            a.clone(),
            Ty::Atom(4),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "HARD_NestedSum".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Sum(
                Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(Ty::Sum(Box::new(c.clone()), Box::new(d.clone()))),
            ),
            Ty::Sum(
                Box::new(Ty::Sum(Box::new(a.clone()), Box::new(c.clone()))),
                Box::new(Ty::Sum(Box::new(b.clone()), Box::new(d.clone()))),
            ),
        ),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "HARD_ContraProd".to_string(),
        ctx: vec![],
        target: chain(vec![
            arr(
                a.clone(),
                Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
            ),
            arr(
                Ty::Sum(Box::new(neg(b.clone())), Box::new(neg(c.clone()))),
                neg(a.clone()),
            ),
        ]),
        expected_provable: true,
    });

    out.push(TheoremCase {
        name: "HARD_MixedDistrib".to_string(),
        ctx: vec![],
        target: arr(
            Ty::Sum(
                Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(Ty::Prod(Box::new(c.clone()), Box::new(d.clone()))),
            ),
            Ty::Prod(
                Box::new(Ty::Sum(Box::new(a.clone()), Box::new(c.clone()))),
                Box::new(Ty::Sum(Box::new(b.clone()), Box::new(d.clone()))),
            ),
        ),
        expected_provable: true,
    });

    out
}

pub fn case_required_corpus() -> Vec<TheoremCase> {
    implication_corpus()
        .into_iter()
        .filter(|c| {
            matches!(
                c.name.as_str(),
                "Sum_elim"
                    | "Sum_comm"
                    | "Sum_assoc"
                    | "Sum_map"
                    | "Sum_prod_distrib_left"
                    | "Sum_prod_distrib_right"
                    | "Sum_bot_left"
                    | "Sum_bot_right"
                    | "HARD_NestedSum"
                    | "HARD_ContraProd"
                    | "HARD_MixedDistrib"
            )
        })
        .collect()
}

pub fn benchmark20_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);

    vec![
        TheoremCase {
            name: "01_I".to_string(),
            ctx: vec![],
            target: arr(a.clone(), a.clone()),
            expected_provable: true,
        },
        TheoremCase {
            name: "02_K".to_string(),
            ctx: vec![],
            target: chain(vec![a.clone(), b.clone(), a.clone()]),
            expected_provable: true,
        },
        TheoremCase {
            name: "03_App".to_string(),
            ctx: vec![],
            target: chain(vec![arr(a.clone(), b.clone()), a.clone(), b.clone()]),
            expected_provable: true,
        },
        TheoremCase {
            name: "04_Comp".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                a.clone(),
                c.clone(),
            ]),
            expected_provable: true,
        },
        TheoremCase {
            name: "05_ProdElimL".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                a.clone(),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "06_ProdElimR".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                b.clone(),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "07_DupPair".to_string(),
            ctx: vec![],
            target: arr(
                a.clone(),
                Ty::Prod(Box::new(a.clone()), Box::new(a.clone())),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "08_ProdComm".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Prod(Box::new(b.clone()), Box::new(a.clone())),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "09_ProdAssoc".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(
                    Box::new(a.clone()),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "10_PairMap".to_string(),
            ctx: vec![],
            target: chain(vec![
                Ty::Prod(
                    Box::new(arr(a.clone(), b.clone())),
                    Box::new(arr(a.clone(), c.clone())),
                ),
                a.clone(),
                Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
            ]),
            expected_provable: true,
        },
        TheoremCase {
            name: "11_SumInl".to_string(),
            ctx: vec![],
            target: arr(a.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
            expected_provable: true,
        },
        TheoremCase {
            name: "12_SumInr".to_string(),
            ctx: vec![],
            target: arr(b.clone(), Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
            expected_provable: true,
        },
        TheoremCase {
            name: "13_SumComm".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                Ty::Sum(Box::new(b.clone()), Box::new(a.clone())),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "14_SumAssoc".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(
                    Box::new(a.clone()),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "15_SumElim".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(a.clone(), c.clone()),
                arr(b.clone(), c.clone()),
                Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
                c.clone(),
            ]),
            expected_provable: true,
        },
        TheoremCase {
            name: "16_ExFalso".to_string(),
            ctx: vec![],
            target: arr(Ty::Bot, a.clone()),
            expected_provable: true,
        },
        TheoremCase {
            name: "17_AndNotToBot".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
                Ty::Bot,
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "18_Explosion".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(a.clone()), Box::new(neg(a.clone()))),
                d.clone(),
            ),
            expected_provable: true,
        },
        TheoremCase {
            name: "19_Contrapositive".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(a.clone(), b.clone()),
                arr(neg(b.clone()), neg(a.clone())),
            ]),
            expected_provable: true,
        },
        TheoremCase {
            name: "20_DeMorganWeak".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
                neg(Ty::Sum(Box::new(a), Box::new(b))),
            ),
            expected_provable: true,
        },
    ]
}

/// Benchmark30: より難しい定理10個を追加
pub fn benchmark30_corpus() -> Vec<TheoremCase> {
    let mut cases = benchmark20_corpus();

    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let d = Ty::Atom(3);
    let e = Ty::Atom(4);
    let f = Ty::Atom(5);

    // 難しい定理10個を追加
    cases.extend(vec![
        // B21: 多重ネストcase (深さ3)
        TheoremCase {
            name: "B21_TripleNested".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(
                    Box::new(a.clone()),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(c.clone()))),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
            ),
            expected_provable: true,
        },
        // B22: 長い関数合成チェーン (6段)
        TheoremCase {
            name: "B22_LongChain".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(e.clone(), f.clone()),
                arr(d.clone(), e.clone()),
                arr(c.clone(), d.clone()),
                arr(b.clone(), c.clone()),
                arr(a.clone(), b.clone()),
                a.clone(),
                f.clone(),
            ]),
            expected_provable: true,
        },
        // B23: 積と和の複雑な分配
        TheoremCase {
            name: "B23_ProdSumDistrib".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
                Ty::Sum(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(c.clone()))),
                ),
            ),
            expected_provable: true,
        },
        // B24: ネストした否定
        TheoremCase {
            name: "B24_DoubleNegIntro".to_string(),
            ctx: vec![],
            target: arr(a.clone(), neg(neg(a.clone()))),
            expected_provable: true,
        },
        // B25: 複雑な対偶
        TheoremCase {
            name: "B25_ContrapositiveProd".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(
                    a.clone(),
                    Ty::Prod(Box::new(b.clone()), Box::new(c.clone())),
                ),
                arr(
                    Ty::Sum(Box::new(neg(b.clone())), Box::new(neg(c.clone()))),
                    neg(a.clone()),
                ),
            ]),
            expected_provable: true,
        },
        // B26: 積の深いネスト
        TheoremCase {
            name: "B26_DeepProdNest".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(c.clone()), Box::new(d.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Prod(Box::new(b.clone()), Box::new(d.clone()))),
                ),
            ),
            expected_provable: true,
        },
        // B27: 和と積の混合
        TheoremCase {
            name: "B27_SumProdMixed".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(
                    Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(c.clone()), Box::new(d.clone()))),
                ),
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(c.clone()))),
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(d.clone()))),
                ),
            ),
            expected_provable: true, // 直観主義論理で証明可能
        },
        // B28: 長い否定連鎖
        TheoremCase {
            name: "B28_NegChain".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(a.clone(), b.clone()),
                arr(b.clone(), c.clone()),
                arr(c.clone(), d.clone()),
                arr(neg(d.clone()), neg(a.clone())),
            ]),
            expected_provable: true,
        },
        // B29: De Morganの完全形
        TheoremCase {
            name: "B29_DeMorganFull".to_string(),
            ctx: vec![],
            target: arr(
                neg(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            ),
            expected_provable: true,
        },
        // B30: 複雑な爆発原理
        TheoremCase {
            name: "B30_ComplexExplosion".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Prod(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(Ty::Prod(Box::new(neg(a.clone())), Box::new(neg(b.clone())))),
                ),
                c.clone(),
            ),
            expected_provable: true,
        },
    ]);

    cases
}

/// 直観主義では証明不可能な定理のテストセット (古典論理では真)
pub fn unprovable_corpus() -> Vec<TheoremCase> {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);

    vec![
        // 排中律 (Law of Excluded Middle)
        TheoremCase {
            name: "UNPROV_LEM".to_string(),
            ctx: vec![],
            target: Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))),
            expected_provable: false,
        },
        // 二重否定除去 (Double Negation Elimination)
        TheoremCase {
            name: "UNPROV_DNE".to_string(),
            ctx: vec![],
            target: arr(neg(neg(a.clone())), a.clone()),
            expected_provable: false,
        },
        // パースの法則 (Peirce's Law)
        TheoremCase {
            name: "UNPROV_Peirce".to_string(),
            ctx: vec![],
            target: arr(arr(arr(a.clone(), b.clone()), a.clone()), a.clone()),
            expected_provable: false,
        },
        // ゲーデル・ダメット論理の公理
        TheoremCase {
            name: "UNPROV_Dummett".to_string(),
            ctx: vec![],
            target: Ty::Sum(
                Box::new(arr(a.clone(), b.clone())),
                Box::new(arr(b.clone(), a.clone())),
            ),
            expected_provable: false,
        },
        // ド・モルガンの法則の逆（積から和へ）
        TheoremCase {
            name: "UNPROV_DeMorganReverse".to_string(),
            ctx: vec![],
            target: arr(
                neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
                Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
            ),
            expected_provable: false,
        },
        // 対偶の逆
        TheoremCase {
            name: "UNPROV_ContraReverse".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(neg(a.clone()), neg(b.clone())),
                arr(b.clone(), a.clone()),
            ]),
            expected_provable: false,
        },
        // 弱い排中律（直観主義では証明可能）
        TheoremCase {
            name: "PROV_WeakLEM".to_string(),
            ctx: vec![],
            target: neg(neg(Ty::Sum(Box::new(a.clone()), Box::new(neg(a.clone()))))),
            expected_provable: true,
        },
        // ド・モルガン（和から積へ、直観主義で証明可能）
        TheoremCase {
            name: "PROV_OrNotToNotAnd".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(Box::new(neg(a.clone())), Box::new(neg(b.clone()))),
                neg(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
            ),
            expected_provable: true,
        },
        // 三段論法の特殊形（直観主義で証明可能）
        TheoremCase {
            name: "PROV_Syllogism".to_string(),
            ctx: vec![],
            target: chain(vec![
                arr(a.clone(), b.clone()),
                arr(b.clone(), c.clone()),
                arr(a.clone(), c.clone()),
            ]),
            expected_provable: true,
        },
        // 和の対称性の別表現（直観主義で証明可能）
        TheoremCase {
            name: "PROV_SumSymm".to_string(),
            ctx: vec![],
            target: arr(
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(c.clone()),
                ),
                Ty::Sum(
                    Box::new(Ty::Sum(Box::new(b.clone()), Box::new(a.clone()))),
                    Box::new(c.clone()),
                ),
            ),
            expected_provable: true,
        },
    ]
}

pub fn run_corpus(
    config: &GAConfig,
    seed: u64,
    repeats: usize,
    limit: Option<usize>,
) -> CorpusReport {
    let mut cases = implication_corpus();
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
    let mut cases = implication_corpus();
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
        let cases = implication_corpus();
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
        for c in implication_corpus()
            .into_iter()
            .filter(|x| x.name.starts_with("IMPOSSIBLE_"))
        {
            assert!(!is_intuitionistic_theorem(&c.ctx, &c.target), "{}", c.name);
        }
    }

    #[test]
    fn impossible_cases_have_small_kripke_countermodels() {
        for c in implication_corpus()
            .into_iter()
            .filter(|x| x.name.starts_with("IMPOSSIBLE_"))
        {
            let cm = find_kripke_countermodel(&c.ctx, &c.target, 4);
            assert!(cm.is_some(), "{}", c.name);
        }
    }

    #[test]
    fn benchmark20_labels_are_machine_checked() {
        let cases = benchmark20_corpus();
        assert_eq!(cases.len(), 20);
        for c in &cases {
            let decided = is_intuitionistic_theorem(&c.ctx, &c.target);
            assert_eq!(
                decided, c.expected_provable,
                "label mismatch: {} expected={} decided={}",
                c.name, c.expected_provable, decided
            );
        }
    }
}
