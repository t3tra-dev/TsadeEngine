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

#[test]
fn free_in_basic() {
    // Var(0) が Var(0) に自由出現する
    assert!(free_in(0, &Tm::Var(0)));
    // Var(1) は Var(0) に自由出現しない
    assert!(!free_in(1, &Tm::Var(0)));
    // Var(0) は λ_.Var(0) 内で束縛される (探索する添字は 1 にシフトされる)
    let lam = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::Var(0)),
    };
    assert!(!free_in(0, &lam));
    // Var(0) は λ_.Var(1) 内で自由出現する
    let lam2 = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::Var(1)),
    };
    assert!(free_in(0, &lam2));
}

#[test]
fn eta_reduce_function() {
    // λx:A. f x → f (where f = Var(1), x = Var(0))
    let tm = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::App(Box::new(Tm::Var(1)), Box::new(Tm::Var(0)))),
    };
    // η 変換後: Var(1) が 1 シフトされ Var(0) になる
    assert_eq!(eta_reduce(&tm), Tm::Var(0));
}

#[test]
fn eta_reduce_no_false_positive() {
    // λx:A. x x は η 変換されない (引数が単に Var(0) を f に適用した形ではない)
    let tm = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::App(Box::new(Tm::Var(0)), Box::new(Tm::Var(0)))),
    };
    assert_eq!(eta_reduce(&tm), tm);
}

#[test]
fn eta_reduce_product() {
    // ⟨fst p, snd p⟩ →  p where p = Var(0)
    let p = Tm::Var(0);
    let tm = Tm::Pair(
        Box::new(Tm::Fst(Box::new(p.clone()))),
        Box::new(Tm::Snd(Box::new(p.clone()))),
    );
    assert_eq!(eta_reduce(&tm), p);
}

#[test]
fn eta_reduce_nested() {
    // λx:A. λy:A. Var(2) y
    // 内側の η 変換: λy. Var(2) y → Var(1) (shift(-1, 0, Var(2)) = Var(1))
    // 外側の body は Var(1) になり f x の形ではないためそれ以上の η 変換は適用しない
    // 結果: λx:A. Var(1)
    let inner = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::App(Box::new(Tm::Var(2)), Box::new(Tm::Var(0)))),
    };
    let outer = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(inner),
    };
    let reduced = eta_reduce(&outer);
    let expected = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::Var(1)),
    };
    assert_eq!(reduced, expected);

    // normalize_eta (β 簡約、次に η 変換) によって完全な連鎖は次のように正規化される:
    // λx:A. (λy:A. Var(2) y) x → β λx:A. Var(1) x → η Var(0)
    let outer_applied = Tm::Lam {
        arg_ty: atom(0),
        body: Box::new(Tm::App(
            Box::new(Tm::Lam {
                arg_ty: atom(0),
                body: Box::new(Tm::App(Box::new(Tm::Var(2)), Box::new(Tm::Var(0)))),
            }),
            Box::new(Tm::Var(0)),
        )),
    };
    assert_eq!(normalize_eta(&outer_applied), Tm::Var(0));
}

#[test]
fn tm_equiv_beta() {
    let a = atom(0);
    // (λx:A. x) y  ≡βη  y
    let redex = Tm::App(
        Box::new(Tm::Lam {
            arg_ty: a.clone(),
            body: Box::new(Tm::Var(0)),
        }),
        Box::new(Tm::Var(0)),
    );
    assert!(tm_equiv(&redex, &Tm::Var(0)));
}

#[test]
fn tm_equiv_eta() {
    let a = atom(0);
    // λx:A. f x  ≡βη f (where f = Var(0))
    let expanded = Tm::Lam {
        arg_ty: a,
        body: Box::new(Tm::App(Box::new(Tm::Var(1)), Box::new(Tm::Var(0)))),
    };
    assert!(tm_equiv(&expanded, &Tm::Var(0)));
}

#[test]
fn tm_equiv_not_equal() {
    assert!(!tm_equiv(&Tm::Var(0), &Tm::Var(1)));
}

#[test]
fn ty_equiv_structural() {
    let a = atom(0);
    let b = atom(1);
    assert!(ty_equiv(&a, &a));
    assert!(!ty_equiv(&a, &b));
    let arr1 = Ty::Arr(Box::new(a.clone()), Box::new(b.clone()));
    let arr2 = Ty::Arr(Box::new(a), Box::new(b));
    assert!(ty_equiv(&arr1, &arr2));
}

#[test]
fn normalize_ty_identity() {
    // 現在、命題論理において normalize_ty は恒等関数
    let ty = Ty::Arr(
        Box::new(Ty::Prod(Box::new(atom(0)), Box::new(atom(1)))),
        Box::new(Ty::Sum(Box::new(atom(2)), Box::new(Ty::Bot))),
    );
    assert_eq!(normalize_ty(&ty), ty);
}

#[test]
fn check_uses_ty_equiv() {
    // `check` が ty_equiv を使用していることを確認 (normalize_ty を通じた構造的等価性)
    // 現在、命題論理においてこれは == だが関数は呼び出される
    let a = atom(0);
    let id = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Var(0)),
    };
    let ty = Ty::Arr(Box::new(a.clone()), Box::new(a));
    assert!(check(&Vec::new(), &id, &ty).is_ok());
}

#[test]
fn check_mismatch_detected() {
    let a = atom(0);
    let b = atom(1);
    let id = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::Var(0)),
    };
    let wrong_ty = Ty::Arr(Box::new(a), Box::new(b));
    assert!(check(&Vec::new(), &id, &wrong_ty).is_err());
}

#[test]
fn subject_reduction_eta() {
    // η 変換された項は型を保持する
    let a = atom(0);
    // λx:A. (λy:B→A. y) x — これは直接 η 変換できないが、簡単なケースをテストする:
    // λx:A. Var(1) x は ctx [A→A] で型 A → ? を持つ; η 変換すると Var(0) になる
    let ctx = vec![Ty::Arr(Box::new(a.clone()), Box::new(a.clone()))];
    let expanded = Tm::Lam {
        arg_ty: a.clone(),
        body: Box::new(Tm::App(Box::new(Tm::Var(1)), Box::new(Tm::Var(0)))),
    };
    let ty_before = infer(&ctx, &expanded).expect("should typecheck");
    let reduced = eta_reduce(&expanded);
    let ty_after = infer(&ctx, &reduced).expect("η-reduced should typecheck");
    assert_eq!(ty_before, ty_after);
}

// --- FOL Phase 1: term-variable operations on types ---

use super::FOTerm;

#[test]
fn ty_term_shift_atom_bot_unchanged() {
    assert_eq!(ty_term_shift(5, 0, &Ty::Atom(0)), Ty::Atom(0));
    assert_eq!(ty_term_shift(5, 0, &Ty::Bot), Ty::Bot);
}

#[test]
fn ty_term_shift_pred_args() {
    let ty = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Var(1)],
    };
    let shifted = ty_term_shift(1, 0, &ty);
    assert_eq!(
        shifted,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(1), FOTerm::Var(2)],
        }
    );
}

#[test]
fn ty_term_shift_forall_increments_cutoff() {
    // ∀. P(Var(0), Var(1)) — Var(0) bound, Var(1) free
    let ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Var(1)],
    }));
    let shifted = ty_term_shift(10, 0, &ty);
    // Var(0) < cutoff=1 → unchanged; Var(1) >= cutoff=1 → Var(11)
    assert_eq!(
        shifted,
        Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0), FOTerm::Var(11)],
        }))
    );
}

#[test]
fn ty_term_shift_nested_forall() {
    // ∀. ∀. P(Var(0), Var(1), Var(2))
    // Var(0), Var(1) bound, Var(2) free
    let ty = Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Var(1), FOTerm::Var(2)],
    }))));
    let shifted = ty_term_shift(1, 0, &ty);
    assert_eq!(
        shifted,
        Ty::Forall(Box::new(Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0), FOTerm::Var(1), FOTerm::Var(3)],
        }))))
    );
}

#[test]
fn ty_term_subst_pred() {
    // P(Var(0)) [0 := Const(42)] → P(Const(42))
    let ty = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    };
    let result = ty_term_subst(0, &FOTerm::Const(42), &ty);
    assert_eq!(
        result,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Const(42)],
        }
    );
}

#[test]
fn ty_term_subst_under_forall() {
    // ∀. P(Var(0), Var(1)) [0 := Const(7)]
    // Var(0) is bound → unchanged; Var(1) is free var 0 → Const(7)
    let ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Var(1)],
    }));
    let result = ty_term_subst(0, &FOTerm::Const(7), &ty);
    assert_eq!(
        result,
        Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0), FOTerm::Const(7)],
        }))
    );
}

#[test]
fn ty_term_subst_bound_var_preserved() {
    // ∀. P(Var(0)) [0 := Const(7)] — Var(0) bound, should not be substituted
    let ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let result = ty_term_subst(0, &FOTerm::Const(7), &ty);
    assert_eq!(result, ty);
}

#[test]
fn ty_term_subst_top_basic() {
    // ∀. P(Var(0)) — subst_top with Const(5) → P(Const(5))
    let body = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    };
    let result = ty_term_subst_top(&FOTerm::Const(5), &body);
    assert_eq!(
        result,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Const(5)],
        }
    );
}

#[test]
fn ty_term_subst_top_shifts_free_vars() {
    // Body = P(Var(0), Var(1))
    // subst_top with Const(5):
    //   shift s up: Const(5) → Const(5)
    //   subst 0: Var(0)→Const(5), Var(1) unchanged
    //   shift down: Var(1)→Var(0)
    //   Result: P(Const(5), Var(0))
    let body = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Var(1)],
    };
    let result = ty_term_subst_top(&FOTerm::Const(5), &body);
    assert_eq!(
        result,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Const(5), FOTerm::Var(0)],
        }
    );
}

#[test]
fn ty_term_subst_arr_propagates() {
    // (P(Var(0)) → P(Var(1))) [0 := Const(3)]
    let ty = Ty::Arr(
        Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0)],
        }),
        Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(1)],
        }),
    );
    let result = ty_term_subst(0, &FOTerm::Const(3), &ty);
    assert_eq!(
        result,
        Ty::Arr(
            Box::new(Ty::Pred {
                sym: 0,
                args: vec![FOTerm::Const(3)],
            }),
            Box::new(Ty::Pred {
                sym: 0,
                args: vec![FOTerm::Var(1)],
            }),
        )
    );
}

#[test]
fn is_intuitionistic_theorem_rejects_fol() {
    // FOL types should return false from the propositional decider
    let fol_ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    assert!(!is_intuitionistic_theorem(&Vec::new(), &fol_ty));
}

#[test]
fn is_intuitionistic_theorem_accepts_ground_one_plus_one() {
    let case = crate::ga::corpus::arith_corpus()
        .into_iter()
        .find(|c| c.name == "C3_OnePlusOne")
        .expect("C3_OnePlusOne exists");
    assert!(is_intuitionistic_theorem(&case.ctx, &case.target));
}

#[test]
fn ty_size_fol_types() {
    let pred = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0), FOTerm::Const(1)],
    };
    assert_eq!(ty_size(&pred), 3); // 1 + 1 + 1

    let forall = Ty::Forall(Box::new(pred.clone()));
    assert_eq!(ty_size(&forall), 4); // 1 + 3

    let exists = Ty::Exists(Box::new(Ty::Bot));
    assert_eq!(ty_size(&exists), 2); // 1 + 1
}

// --- FOL Phase 2: Proof term constructs ---

#[test]
fn tlam_intro_typing() {
    // Λ. Var(0) in context [P(Var(0))]
    // Shifted ctx: [P(Var(1))], body Var(0) has type P(Var(1))
    // Result: ∀. P(Var(1))  — but wait, the body's type uses shifted vars
    // Actually let's use a simpler example: empty ctx, body is a proof of an atom
    // Λ. x0 where ctx = [A0] → shifted ctx = [A0] (Atom has no term vars)
    // body Var(0) : A0, so TLam : ∀. A0
    let ctx = vec![Ty::Atom(0)];
    let tm = Tm::TLam {
        body: Box::new(Tm::Var(0)),
    };
    let ty = infer(&ctx, &tm).expect("TLam should typecheck");
    assert_eq!(ty, Ty::Forall(Box::new(Ty::Atom(0))));
}

#[test]
fn tlam_intro_with_pred() {
    // ctx = [P(Var(0))], Λ. Var(0)
    // shifted ctx = [P(Var(1))], body Var(0) : P(Var(1))
    // Result: ∀. P(Var(1))
    let ctx = vec![Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }];
    let tm = Tm::TLam {
        body: Box::new(Tm::Var(0)),
    };
    let ty = infer(&ctx, &tm).expect("TLam with pred should typecheck");
    assert_eq!(
        ty,
        Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(1)],
        }))
    );
}

#[test]
fn tapp_elim_typing() {
    // Given proof of ∀. P(Var(0)), TApp with Const(5) yields P(Const(5))
    let forall_ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let ctx = vec![forall_ty.clone()];
    let tm = Tm::TApp {
        term: Box::new(Tm::Var(0)),
        witness: FOTerm::Const(5),
    };
    let ty = infer(&ctx, &tm).expect("TApp should typecheck");
    assert_eq!(
        ty,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Const(5)],
        }
    );
}

#[test]
fn pack_typing() {
    // pack(Const(7), proof) as ∃. P(Var(0))
    // Need body : P(Const(7))
    let exists_ty = Ty::Exists(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let body_ty = Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Const(7)],
    };
    let ctx = vec![body_ty];
    let tm = Tm::Pack {
        witness: FOTerm::Const(7),
        body: Box::new(Tm::Var(0)),
        exists_ty: exists_ty.clone(),
    };
    let ty = infer(&ctx, &tm).expect("Pack should typecheck");
    assert_eq!(ty, exists_ty);
}

#[test]
fn unpack_typing() {
    // Given ∃. P(Var(0)), unpack with body that produces A0 (no term var)
    // ctx = [∃. P(Var(0)), A0 → A0]
    // scrut = Var(1) : ∃. P(Var(0))
    // In unpack body: shifted ctx + P(Var(0)) pushed
    // body = Var(1) which will have type from shifted ctx entry for A0 → A0
    // Actually let's keep it simple:
    // ctx = [∃. P(Var(0))], scrut = Var(0)
    // shifted ctx = [∃. P(Var(1))], then push P(Var(0))
    // body needs to produce something without term var 0
    // body = Lam { arg_ty: A0, body: Var(0) } : A0 → A0 (no term vars)
    let exists_ty = Ty::Exists(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let ctx = vec![exists_ty];
    let tm = Tm::Unpack {
        scrut: Box::new(Tm::Var(0)),
        body: Box::new(Tm::Lam {
            arg_ty: Ty::Atom(0),
            body: Box::new(Tm::Var(0)),
        }),
    };
    let ty = infer(&ctx, &tm).expect("Unpack should typecheck");
    assert_eq!(ty, Ty::Arr(Box::new(Ty::Atom(0)), Box::new(Ty::Atom(0))));
}

#[test]
fn tapp_on_non_forall_error() {
    let ctx = vec![Ty::Atom(0)];
    let tm = Tm::TApp {
        term: Box::new(Tm::Var(0)),
        witness: FOTerm::Const(0),
    };
    let err = infer(&ctx, &tm).expect_err("must fail");
    assert!(matches!(err, TypeError::NotAForall { .. }));
}

#[test]
fn unpack_on_non_exists_error() {
    let ctx = vec![Ty::Atom(0)];
    let tm = Tm::Unpack {
        scrut: Box::new(Tm::Var(0)),
        body: Box::new(Tm::Var(0)),
    };
    let err = infer(&ctx, &tm).expect_err("must fail");
    assert!(matches!(err, TypeError::NotAnExists { .. }));
}

#[test]
fn pack_wrong_exists_ty_error() {
    // exists_ty is not ∃.φ
    let ctx = vec![Ty::Atom(0)];
    let tm = Tm::Pack {
        witness: FOTerm::Const(0),
        body: Box::new(Tm::Var(0)),
        exists_ty: Ty::Atom(0),
    };
    let err = infer(&ctx, &tm).expect_err("must fail");
    assert!(matches!(err, TypeError::NotAnExists { .. }));
}

#[test]
fn tapp_tlam_beta_reduction() {
    // TApp(TLam{body}, witness) → tm_term_subst_top(witness, body)
    // TLam body = Var(0) (a proof var), witness = Const(5)
    // After reduction: tm_term_subst_top(Const(5), Var(0)) = Var(0) (proof vars unaffected)
    let tm = Tm::TApp {
        term: Box::new(Tm::TLam {
            body: Box::new(Tm::Var(0)),
        }),
        witness: FOTerm::Const(5),
    };
    let nf = normalize(&tm);
    assert_eq!(nf, Tm::Var(0));
}

#[test]
fn unpack_pack_beta_reduction() {
    // Unpack(Pack{w, p, _}, body) → subst_top(p, &tm_term_subst_top(w, body))
    // Pack: witness=Const(3), body=Var(0) (proof of P(Const(3)))
    // Unpack body: Var(0) (bound proof var referencing the opened proof)
    // Result: subst_top(Var(0)_proof, tm_term_subst_top(Const(3), Var(0)))
    //       = subst_top(Var(0), Var(0)) = Var(0)
    let exists_ty = Ty::Exists(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let tm = Tm::Unpack {
        scrut: Box::new(Tm::Pack {
            witness: FOTerm::Const(3),
            body: Box::new(Tm::Var(0)),
            exists_ty,
        }),
        body: Box::new(Tm::Var(0)),
    };
    let nf = normalize(&tm);
    assert_eq!(nf, Tm::Var(0));
}

#[test]
fn subject_reduction_tlam_tapp() {
    // Build a well-typed TApp(TLam{...}, witness) and check type is preserved
    // ctx = [P(Var(0))]
    // TLam { body: Var(0) } : ∀. P(Var(1))  (ctx shifted up)
    // TApp with Const(5):  P(Var(1))[0:=Const(5)] — but Var(1) is free, so P(Var(0)) after shift-down
    // Wait, let me think more carefully.
    //
    // ctx = [∀. P(Var(0))], tm = TApp { term: Var(0), witness: Const(5) }
    // Var(0) : ∀. P(Var(0))
    // TApp yields P(Var(0))[0:=Const(5)] = P(Const(5))
    let forall_ty = Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let ctx = vec![forall_ty];
    let tm = Tm::TApp {
        term: Box::new(Tm::Var(0)),
        witness: FOTerm::Const(5),
    };
    let ty_before = infer(&ctx, &tm).expect("typed");
    // Build a redex: TApp(TLam{body}, Const(5))
    // ctx = [∀. P(Var(0))]
    // Inside TLam, shifted ctx = [∀. P(Var(1))]
    // body = TApp { Var(0), Var(0) }: Var(0) : ∀. P(Var(1)), TApp with FOTerm::Var(0) → P(Var(1))[0:=Var(0)] = P(Var(0))
    // TLam : ∀. P(Var(0))
    // TApp with Const(5): P(Var(0))[0:=Const(5)] = P(Const(5))
    let ctx2 = vec![Ty::Forall(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }))];
    let redex = Tm::TApp {
        term: Box::new(Tm::TLam {
            body: Box::new(Tm::TApp {
                term: Box::new(Tm::Var(0)),
                witness: FOTerm::Var(0),
            }),
        }),
        witness: FOTerm::Const(5),
    };
    let ty_before2 = infer(&ctx2, &redex).expect("redex should typecheck");
    let nf = normalize(&redex);
    let ty_after = infer(&ctx2, &nf).expect("normal form should typecheck");
    assert_eq!(ty_before2, ty_after);
    assert_eq!(
        ty_before,
        Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Const(5)],
        }
    );
}

#[test]
fn tm_term_shift_basic() {
    // TApp { term: Var(0), witness: FOTerm::Var(0) } shifted by 1
    // Var(0) is proof var → unchanged, FOTerm::Var(0) → FOTerm::Var(1)
    let tm = Tm::TApp {
        term: Box::new(Tm::Var(0)),
        witness: FOTerm::Var(0),
    };
    let shifted = tm_term_shift(1, 0, &tm);
    assert_eq!(
        shifted,
        Tm::TApp {
            term: Box::new(Tm::Var(0)),
            witness: FOTerm::Var(1),
        }
    );
}

#[test]
fn tm_term_shift_under_tlam() {
    // TLam { body: TApp { Var(0), FOTerm::Var(0) } } shifted by 1
    // TLam binds term var → cutoff increments
    // FOTerm::Var(0) < cutoff=1 → unchanged
    let tm = Tm::TLam {
        body: Box::new(Tm::TApp {
            term: Box::new(Tm::Var(0)),
            witness: FOTerm::Var(0),
        }),
    };
    let shifted = tm_term_shift(1, 0, &tm);
    assert_eq!(
        shifted,
        Tm::TLam {
            body: Box::new(Tm::TApp {
                term: Box::new(Tm::Var(0)),
                witness: FOTerm::Var(0),
            }),
        }
    );
}

#[test]
fn tm_term_subst_top_basic() {
    // TApp { Var(0), FOTerm::Var(0) } with subst_top(Const(9))
    // FOTerm::Var(0) → Const(9), proof Var(0) unchanged
    let tm = Tm::TApp {
        term: Box::new(Tm::Var(0)),
        witness: FOTerm::Var(0),
    };
    let result = tm_term_subst_top(&FOTerm::Const(9), &tm);
    assert_eq!(
        result,
        Tm::TApp {
            term: Box::new(Tm::Var(0)),
            witness: FOTerm::Const(9),
        }
    );
}

#[test]
fn unpack_term_var_escapes() {
    // Unpack where body type mentions term var 0 → should error
    // ctx = [∃. P(Var(0))], body produces P(Var(0)) which mentions term var 0
    let exists_ty = Ty::Exists(Box::new(Ty::Pred {
        sym: 0,
        args: vec![FOTerm::Var(0)],
    }));
    let ctx = vec![exists_ty];
    // body = Var(0) : P(Var(0)) — the opened type, which mentions term var 0
    let tm = Tm::Unpack {
        scrut: Box::new(Tm::Var(0)),
        body: Box::new(Tm::Var(0)),
    };
    let err = infer(&ctx, &tm).expect_err("must fail: term var escapes");
    assert!(matches!(err, TypeError::TermVarEscapes));
}

#[test]
fn ty_term_free_in_basic() {
    assert!(ty_term_free_in(
        0,
        &Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0)]
        }
    ));
    assert!(!ty_term_free_in(0, &Ty::Atom(0)));
    assert!(!ty_term_free_in(0, &Ty::Bot));
    // Under Forall: var 0 becomes var 1
    assert!(!ty_term_free_in(
        0,
        &Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0)]
        }))
    ));
    assert!(ty_term_free_in(
        0,
        &Ty::Forall(Box::new(Ty::Pred {
            sym: 0,
            args: vec![FOTerm::Var(1)]
        }))
    ));
}
