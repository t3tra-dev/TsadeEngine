use std::collections::HashSet;

use super::*;

fn atom(n: u32) -> Ty {
    Ty::Atom(n)
}

fn enum_types(max_depth: usize, atoms: &[u32]) -> Vec<Ty> {
    let mut acc: HashSet<Ty> = atoms.iter().copied().map(Ty::Atom).collect();
    let mut frontier: Vec<Ty> = acc.iter().cloned().collect();
    for _ in 0..max_depth {
        let mut next: Vec<Ty> = Vec::new();
        for a in &frontier {
            for b in &frontier {
                let arr = Ty::Arr(Box::new(a.clone()), Box::new(b.clone()));
                let prod = Ty::Prod(Box::new(a.clone()), Box::new(b.clone()));
                let sum = Ty::Sum(Box::new(a.clone()), Box::new(b.clone()));
                if acc.insert(arr.clone()) {
                    next.push(arr);
                }
                if acc.insert(prod.clone()) {
                    next.push(prod);
                }
                if acc.insert(sum.clone()) {
                    next.push(sum);
                }
                acc.insert(Ty::Bot);
            }
        }
        if next.is_empty() {
            break;
        }
        frontier.extend(next);
        if frontier.len() > 32 {
            frontier.truncate(32);
        }
    }
    acc.into_iter().collect()
}

fn enum_terms(ctx: &Ctx, depth: usize, tys: &[Ty], cap: usize) -> Vec<Tm> {
    let mut out = Vec::new();

    for i in 0..ctx.len() {
        out.push(Tm::Var(i as u32));
        if out.len() >= cap {
            return out;
        }
    }

    if depth == 0 {
        return out;
    }

    let sub = enum_terms(ctx, depth - 1, tys, cap / 2 + 1);

    for arg_ty in tys.iter().take(8) {
        let mut ext = ctx.clone();
        ext.push(arg_ty.clone());
        for body in enum_terms(&ext, depth - 1, tys, 16) {
            out.push(Tm::Lam {
                arg_ty: arg_ty.clone(),
                body: Box::new(body),
            });
            if out.len() >= cap {
                return out;
            }
        }
    }

    for a in sub.iter().take(20) {
        for b in sub.iter().take(20) {
            out.push(Tm::App(Box::new(a.clone()), Box::new(b.clone())));
            out.push(Tm::Pair(Box::new(a.clone()), Box::new(b.clone())));
            out.push(Tm::Inl {
                rhs_ty: Ty::Atom(0),
                term: Box::new(a.clone()),
            });
            out.push(Tm::Inr {
                lhs_ty: Ty::Atom(0),
                term: Box::new(a.clone()),
            });
            if out.len() >= cap {
                return out;
            }
        }
        out.push(Tm::Fst(Box::new(a.clone())));
        out.push(Tm::Snd(Box::new(a.clone())));
        out.push(Tm::Absurd {
            bot_term: Box::new(a.clone()),
            target_ty: Ty::Atom(0),
        });
        out.push(Tm::Case {
            scrut: Box::new(a.clone()),
            left: Box::new(Tm::Var(0)),
            right: Box::new(Tm::Var(0)),
        });
        if out.len() >= cap {
            return out;
        }
    }

    out
}

#[test]
fn infer_id() {
    let a = atom(0);
    let tm = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Var(0)),
    };
    let ty = infer(&Vec::new(), &tm).expect("id should typecheck");
    assert_eq!(ty, Ty::Arr(Box::new(a.clone()), Box::new(a)));
}

#[test]
fn infer_k_combinator() {
    let a = atom(0);
    let b = atom(1);
    let tm = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Lam {
            arg_ty: b.clone(),
            body: Box::new(Tm::Var(1)),
        }),
    };

    let expected = Ty::Arr(
        Box::new(a.clone()),
        Box::new(Ty::Arr(Box::new(b), Box::new(a))),
    );
    assert_eq!(infer(&Vec::new(), &tm), Ok(expected));
}

#[test]
fn infer_prod_terms() {
    let a = atom(0);
    let b = atom(1);
    let pair = Tm::Pair(Box::new(Tm::Var(1)), Box::new(Tm::Var(0)));
    let ctx = vec![a.clone(), b.clone()];
    let ty = infer(&ctx, &pair).expect("pair typechecks");
    assert_eq!(ty, Ty::Prod(Box::new(a.clone()), Box::new(b.clone())));

    let fst = Tm::Fst(Box::new(pair.clone()));
    let snd = Tm::Snd(Box::new(pair));
    assert_eq!(infer(&ctx, &fst), Ok(a));
    assert_eq!(infer(&ctx, &snd), Ok(b));
}

#[test]
fn infer_sum_terms() {
    let a = atom(0);
    let b = atom(1);
    let inl = Tm::Inl {
        rhs_ty: b.clone(),
        term: Box::new(Tm::Var(0)),
    };
    let ctx = vec![a.clone()];
    assert_eq!(
        infer(&ctx, &inl),
        Ok(Ty::Sum(Box::new(a.clone()), Box::new(b.clone())))
    );

    let scrut = Tm::Var(0);
    let case = Tm::Case {
        scrut: Box::new(scrut),
        left: Box::new(Tm::Var(0)),
        right: Box::new(Tm::Var(0)),
    };
    let ctx_case = vec![Ty::Sum(Box::new(a.clone()), Box::new(a.clone()))];
    assert_eq!(infer(&ctx_case, &case), Ok(a));
}

#[test]
fn infer_var_out_of_range() {
    let err = infer(&Vec::new(), &Tm::Var(0)).expect_err("must fail");
    assert!(matches!(err, TypeError::UnboundVar { .. }));
}

#[test]
fn infer_app_not_function() {
    let ctx = vec![atom(0)];
    let tm = Tm::App(Box::new(Tm::Var(0)), Box::new(Tm::Var(0)));
    let err = infer(&ctx, &tm).expect_err("must fail");
    assert!(matches!(err, TypeError::NotAFunction { .. }));
}

#[test]
fn shift_examples() {
    assert_eq!(shift(1, 0, &Tm::Var(0)), Tm::Var(1));
    assert_eq!(shift(1, 1, &Tm::Var(0)), Tm::Var(0));
}

#[test]
fn beta_reduces_to_argument() {
    let a = atom(0);
    let arg = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Var(0)),
    };
    let app = Tm::App(
        Box::new(Tm::Lam {
            arg_ty: a,
            body: Box::new(Tm::Var(0)),
        }),
        Box::new(arg.clone()),
    );
    assert_eq!(normalize(&app), arg);
}

#[test]
fn pair_projection_reduces() {
    let tm = Tm::Fst(Box::new(Tm::Pair(
        Box::new(Tm::Var(1)),
        Box::new(Tm::Var(0)),
    )));
    assert_eq!(normalize(&tm), Tm::Var(1));
}

#[test]
fn case_inl_reduces() {
    let tm = Tm::Case {
        scrut: Box::new(Tm::Inl {
            rhs_ty: Ty::Atom(1),
            term: Box::new(Tm::Var(0)),
        }),
        left: Box::new(Tm::Var(0)),
        right: Box::new(Tm::Var(0)),
    };
    assert_eq!(normalize(&tm), Tm::Var(0));
}

#[test]
fn case_inr_reduces() {
    let tm = Tm::Case {
        scrut: Box::new(Tm::Inr {
            lhs_ty: Ty::Atom(1),
            term: Box::new(Tm::Var(0)),
        }),
        left: Box::new(Tm::Var(0)),
        right: Box::new(Tm::Var(0)),
    };
    assert_eq!(normalize(&tm), Tm::Var(0));
}

#[test]
fn subject_reduction_simple() {
    let a = atom(0);
    let id = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Var(0)),
    };
    let tm = Tm::App(Box::new(id), Box::new(Tm::Var(0)));
    let ctx = vec![a];
    let before = infer(&ctx, &tm).expect("typed");
    let nf = normalize(&tm);
    let after = infer(&ctx, &nf).expect("typed after normalize");
    assert_eq!(before, after);
}

#[test]
fn property_like_subject_reduction_and_nf_idempotence() {
    let tys = enum_types(1, &[0, 1]);
    let ctxs = vec![
        vec![],
        vec![Ty::Atom(0)],
        vec![Ty::Atom(1), Ty::Atom(0)],
        vec![Ty::Prod(Box::new(Ty::Atom(0)), Box::new(Ty::Atom(1)))],
    ];

    for ctx in ctxs {
        let terms = enum_terms(&ctx, 2, &tys, 180);
        for tm in terms {
            if let Ok(ty_before) = infer(&ctx, &tm) {
                let nf = normalize(&tm);
                let ty_after = infer(&ctx, &nf).expect("normalized term should be typable");
                assert_eq!(ty_before, ty_after, "tm={tm:?} nf={nf:?}");

                let nf2 = normalize(&nf);
                assert_eq!(nf, nf2, "normalize should be idempotent for nf={nf:?}");
            }
        }
    }
}

#[test]
fn decider_matches_basic_examples() {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let i = Ty::Arr(Box::new(a.clone()), Box::new(a.clone()));
    let k = Ty::Arr(
        Box::new(a.clone()),
        Box::new(Ty::Arr(Box::new(b.clone()), Box::new(a.clone()))),
    );
    let impossible = Ty::Arr(Box::new(a.clone()), Box::new(b));

    assert!(is_intuitionistic_theorem(&Vec::new(), &i));
    assert!(is_intuitionistic_theorem(&Vec::new(), &k));
    assert!(!is_intuitionistic_theorem(&Vec::new(), &impossible));
}

#[test]
fn decider_handles_prod() {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let intro = Ty::Arr(
        Box::new(a.clone()),
        Box::new(Ty::Arr(
            Box::new(b.clone()),
            Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
        )),
    );
    let elim_l = Ty::Arr(
        Box::new(Ty::Prod(Box::new(a.clone()), Box::new(b.clone()))),
        Box::new(a),
    );
    assert!(is_intuitionistic_theorem(&Vec::new(), &intro));
    assert!(is_intuitionistic_theorem(&Vec::new(), &elim_l));
}

#[test]
fn decider_handles_sum() {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let intro_l = Ty::Arr(
        Box::new(a.clone()),
        Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
    );
    let elim = Ty::Arr(
        Box::new(Ty::Sum(Box::new(a.clone()), Box::new(b.clone()))),
        Box::new(Ty::Arr(
            Box::new(Ty::Arr(Box::new(a.clone()), Box::new(Ty::Atom(2)))),
            Box::new(Ty::Arr(
                Box::new(Ty::Arr(Box::new(b.clone()), Box::new(Ty::Atom(2)))),
                Box::new(Ty::Atom(2)),
            )),
        )),
    );
    assert!(is_intuitionistic_theorem(&Vec::new(), &intro_l));
    assert!(is_intuitionistic_theorem(&Vec::new(), &elim));
}

#[test]
fn absurd_typing_and_decider_bot() {
    let a = Ty::Atom(0);
    let ctx = vec![Ty::Bot];
    let tm = Tm::Absurd {
        bot_term: Box::new(Tm::Var(0)),
        target_ty: a.clone(),
    };
    assert_eq!(infer(&ctx, &tm), Ok(a.clone()));
    assert!(is_intuitionistic_theorem(&ctx, &a));
}

#[test]
fn kripke_finds_countermodel_for_non_theorem() {
    let a = Ty::Atom(0);
    let b = Ty::Atom(1);
    let goal = Ty::Arr(Box::new(a), Box::new(b));
    let cm = find_kripke_countermodel(&Vec::new(), &goal, 3);
    assert!(cm.is_some());
}

#[test]
fn kripke_no_countermodel_for_theorem_small_search() {
    let a = Ty::Atom(0);
    let goal = Ty::Arr(Box::new(a.clone()), Box::new(a));
    let cm = find_kripke_countermodel(&Vec::new(), &goal, 3);
    assert!(cm.is_none());
}
