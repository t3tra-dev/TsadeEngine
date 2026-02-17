use super::*;
use crate::kernel::{Tm, Ty};

struct FixedChoices(Vec<u32>, usize);
impl ChoiceStream for FixedChoices {
    fn next_u32(&mut self) -> u32 {
        if self.0.is_empty() {
            return 0;
        }
        let v = self.0[self.1 % self.0.len()];
        self.1 += 1;
        v
    }
}

#[test]
fn beam_finds_identity() {
    let a = Ty::Atom(0);
    let target = Ty::Arr(Box::new(a.clone()), Box::new(a));
    let ctx = Vec::new();
    let mut c = FixedChoices(vec![0, 1, 2, 3, 4], 0);
    let out = beam_search(
        &ctx,
        &target,
        &mut c,
        &SearchConfig {
            beam_width: 8,
            max_iters: 24,
            expand_per_state: 3,
            synth_budget: 8,
        },
        &SearchPolicy::default(),
    );

    let tm = out.complete_term.expect("should finalize");
    assert!(matches!(tm, Tm::Lam { .. }));
}

#[test]
fn dedup_and_memo_work() {
    let a = Ty::Atom(0);
    let target = Ty::Arr(Box::new(a.clone()), Box::new(a));
    let mut c = FixedChoices(vec![1, 2, 3, 4, 5, 6, 7, 8], 0);
    let out = beam_search(
        &Vec::new(),
        &target,
        &mut c,
        &SearchConfig {
            beam_width: 6,
            max_iters: 18,
            expand_per_state: 3,
            synth_budget: 6,
        },
        &SearchPolicy::default(),
    );
    assert!(out.metrics.dedup_dropped > 0 || out.metrics.memo_hits > 0);
}

#[test]
fn beam_handles_sum_intro() {
    let target = Ty::Arr(
        Box::new(Ty::Atom(0)),
        Box::new(Ty::Sum(Box::new(Ty::Atom(0)), Box::new(Ty::Atom(1)))),
    );
    let mut c = FixedChoices(vec![0, 0, 0, 0], 0);
    let out = beam_search(
        &Vec::new(),
        &target,
        &mut c,
        &SearchConfig {
            beam_width: 8,
            max_iters: 20,
            expand_per_state: 3,
            synth_budget: 8,
        },
        &SearchPolicy::default(),
    );
    assert!(out.complete_term.is_some());
}

#[test]
fn beam_handles_case_with_sum_assumption() {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let c = Ty::Atom(2);
    let ctx = vec![
        Ty::Sum(Box::new(a.clone()), Box::new(b.clone())),
        Ty::Arr(Box::new(a.clone()), Box::new(c.clone())),
        Ty::Arr(Box::new(b.clone()), Box::new(c.clone())),
    ];
    let scruts = super::engine::collect_case_scrutinees(&ctx);
    assert!(!scruts.is_empty());
    assert!(scruts.iter().any(|t| matches!(t, PTm::Var(_))));
    let mut ch = FixedChoices(vec![5, 5, 0, 1, 2, 3, 4, 5, 6, 7], 0);
    let out = beam_search(
        &ctx,
        &c,
        &mut ch,
        &SearchConfig {
            beam_width: 16,
            max_iters: 30,
            expand_per_state: 3,
            synth_budget: 8,
        },
        &SearchPolicy::default(),
    );
    assert!(out.metrics.expanded_states > 0);
}

#[test]
fn pretty_prints_readably() {
    let ty = Ty::Arr(
        Box::new(Ty::Atom(0)),
        Box::new(Ty::Prod(Box::new(Ty::Atom(1)), Box::new(Ty::Atom(2)))),
    );
    assert!(pretty_ty(&ty).contains("->"));

    let tm = Tm::Lam {
        arg_ty: Ty::Atom(0),
        body: Box::new(Tm::Var(0)),
    };
    assert!(pretty_tm(&tm).contains("x0"));
}
