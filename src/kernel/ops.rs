use super::syntax::fo_term_size;
use super::{FOTerm, Tm, Ty};

fn shift_index(k: u32, d: i32) -> u32 {
    let next = (k as i64) + (d as i64);
    if next < 0 { 0 } else { next as u32 }
}

pub fn shift(d: i32, cutoff: u32, tm: &Tm) -> Tm {
    match tm {
        Tm::Var(k) => {
            if *k >= cutoff {
                Tm::Var(shift_index(*k, d))
            } else {
                Tm::Var(*k)
            }
        }
        Tm::Lam { arg_ty, body } => Tm::Lam {
            arg_ty: arg_ty.clone(),
            body: Box::new(shift(d, cutoff + 1, body)),
        },
        Tm::App(f, x) => Tm::App(Box::new(shift(d, cutoff, f)), Box::new(shift(d, cutoff, x))),
        Tm::Pair(a, b) => Tm::Pair(Box::new(shift(d, cutoff, a)), Box::new(shift(d, cutoff, b))),
        Tm::Fst(t) => Tm::Fst(Box::new(shift(d, cutoff, t))),
        Tm::Snd(t) => Tm::Snd(Box::new(shift(d, cutoff, t))),
        Tm::Inl { rhs_ty, term } => Tm::Inl {
            rhs_ty: rhs_ty.clone(),
            term: Box::new(shift(d, cutoff, term)),
        },
        Tm::Inr { lhs_ty, term } => Tm::Inr {
            lhs_ty: lhs_ty.clone(),
            term: Box::new(shift(d, cutoff, term)),
        },
        Tm::Case { scrut, left, right } => Tm::Case {
            scrut: Box::new(shift(d, cutoff, scrut)),
            left: Box::new(shift(d, cutoff + 1, left)),
            right: Box::new(shift(d, cutoff + 1, right)),
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => Tm::Absurd {
            bot_term: Box::new(shift(d, cutoff, bot_term)),
            target_ty: target_ty.clone(),
        },
        Tm::TLam { body } => Tm::TLam {
            body: Box::new(shift(d, cutoff, body)),
        },
        Tm::TApp { term, witness } => Tm::TApp {
            term: Box::new(shift(d, cutoff, term)),
            witness: witness.clone(),
        },
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => Tm::Pack {
            witness: witness.clone(),
            body: Box::new(shift(d, cutoff, body)),
            exists_ty: exists_ty.clone(),
        },
        Tm::Unpack { scrut, body } => Tm::Unpack {
            scrut: Box::new(shift(d, cutoff, scrut)),
            body: Box::new(shift(d, cutoff + 1, body)),
        },
        Tm::Refl { term } => Tm::Refl { term: term.clone() },
        Tm::Subst {
            eq_proof,
            body,
            motive,
        } => Tm::Subst {
            eq_proof: Box::new(shift(d, cutoff, eq_proof)),
            body: Box::new(shift(d, cutoff, body)),
            motive: motive.clone(),
        },
    }
}

pub fn subst(j: u32, s: &Tm, tm: &Tm) -> Tm {
    fn walk(c: u32, j: u32, s: &Tm, tm: &Tm) -> Tm {
        match tm {
            Tm::Var(k) => {
                if *k == j + c {
                    shift(c as i32, 0, s)
                } else {
                    Tm::Var(*k)
                }
            }
            Tm::Lam { arg_ty, body } => Tm::Lam {
                arg_ty: arg_ty.clone(),
                body: Box::new(walk(c + 1, j, s, body)),
            },
            Tm::App(f, x) => Tm::App(Box::new(walk(c, j, s, f)), Box::new(walk(c, j, s, x))),
            Tm::Pair(a, b) => Tm::Pair(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            Tm::Fst(t) => Tm::Fst(Box::new(walk(c, j, s, t))),
            Tm::Snd(t) => Tm::Snd(Box::new(walk(c, j, s, t))),
            Tm::Inl { rhs_ty, term } => Tm::Inl {
                rhs_ty: rhs_ty.clone(),
                term: Box::new(walk(c, j, s, term)),
            },
            Tm::Inr { lhs_ty, term } => Tm::Inr {
                lhs_ty: lhs_ty.clone(),
                term: Box::new(walk(c, j, s, term)),
            },
            Tm::Case { scrut, left, right } => Tm::Case {
                scrut: Box::new(walk(c, j, s, scrut)),
                left: Box::new(walk(c + 1, j, s, left)),
                right: Box::new(walk(c + 1, j, s, right)),
            },
            Tm::Absurd {
                bot_term,
                target_ty,
            } => Tm::Absurd {
                bot_term: Box::new(walk(c, j, s, bot_term)),
                target_ty: target_ty.clone(),
            },
            Tm::TLam { body } => Tm::TLam {
                body: Box::new(walk(c, j, s, body)),
            },
            Tm::TApp { term, witness } => Tm::TApp {
                term: Box::new(walk(c, j, s, term)),
                witness: witness.clone(),
            },
            Tm::Pack {
                witness,
                body,
                exists_ty,
            } => Tm::Pack {
                witness: witness.clone(),
                body: Box::new(walk(c, j, s, body)),
                exists_ty: exists_ty.clone(),
            },
            Tm::Unpack { scrut, body } => Tm::Unpack {
                scrut: Box::new(walk(c, j, s, scrut)),
                body: Box::new(walk(c + 1, j, s, body)),
            },
            Tm::Refl { term } => Tm::Refl { term: term.clone() },
            Tm::Subst {
                eq_proof,
                body,
                motive,
            } => Tm::Subst {
                eq_proof: Box::new(walk(c, j, s, eq_proof)),
                body: Box::new(walk(c, j, s, body)),
                motive: motive.clone(),
            },
        }
    }

    walk(0, j, s, tm)
}

pub fn subst_top(s: &Tm, body: &Tm) -> Tm {
    let s_up = shift(1, 0, s);
    let body_sub = subst(0, &s_up, body);
    shift(-1, 0, &body_sub)
}

// --- FOTerm shift / subst (term-variable operations) ---

pub fn fo_term_shift(d: i32, cutoff: u32, tm: &FOTerm) -> FOTerm {
    match tm {
        FOTerm::Var(i) => {
            if *i >= cutoff {
                let next = ((*i as i64) + (d as i64)).max(0) as u32;
                FOTerm::Var(next)
            } else {
                FOTerm::Var(*i)
            }
        }
        FOTerm::Const(c) => FOTerm::Const(*c),
        FOTerm::Func { sym, args } => FOTerm::Func {
            sym: *sym,
            args: args.iter().map(|a| fo_term_shift(d, cutoff, a)).collect(),
        },
    }
}

pub fn fo_term_subst(j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
    fn walk(c: u32, j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
        match tm {
            FOTerm::Var(i) => {
                if *i == j + c {
                    fo_term_shift(c as i32, 0, s)
                } else {
                    FOTerm::Var(*i)
                }
            }
            FOTerm::Const(k) => FOTerm::Const(*k),
            FOTerm::Func { sym, args } => FOTerm::Func {
                sym: *sym,
                args: args.iter().map(|a| walk(c, j, s, a)).collect(),
            },
        }
    }
    walk(0, j, s, tm)
}

pub fn fo_term_subst_top(s: &FOTerm, body: &FOTerm) -> FOTerm {
    let su = fo_term_shift(1, 0, s);
    let sub = fo_term_subst(0, &su, body);
    fo_term_shift(-1, 0, &sub)
}

// --- Type-level term-variable operations ---

/// Shift term variables in a type by `d`, with cutoff `cutoff`.
/// Forall/Exists bind term variables, so cutoff increments under them.
pub fn ty_term_shift(d: i32, cutoff: u32, ty: &Ty) -> Ty {
    match ty {
        Ty::Atom(_) | Ty::Bot => ty.clone(),
        Ty::Pred { sym, args } => Ty::Pred {
            sym: *sym,
            args: args.iter().map(|a| fo_term_shift(d, cutoff, a)).collect(),
        },
        Ty::Arr(a, b) => Ty::Arr(
            Box::new(ty_term_shift(d, cutoff, a)),
            Box::new(ty_term_shift(d, cutoff, b)),
        ),
        Ty::Prod(a, b) => Ty::Prod(
            Box::new(ty_term_shift(d, cutoff, a)),
            Box::new(ty_term_shift(d, cutoff, b)),
        ),
        Ty::Sum(a, b) => Ty::Sum(
            Box::new(ty_term_shift(d, cutoff, a)),
            Box::new(ty_term_shift(d, cutoff, b)),
        ),
        Ty::Forall(body) => Ty::Forall(Box::new(ty_term_shift(d, cutoff + 1, body))),
        Ty::Exists(body) => Ty::Exists(Box::new(ty_term_shift(d, cutoff + 1, body))),
        Ty::Eq(s, t) => Ty::Eq(fo_term_shift(d, cutoff, s), fo_term_shift(d, cutoff, t)),
    }
}

/// Substitute term variable `j` with FOTerm `s` in a type.
pub fn ty_term_subst(j: u32, s: &FOTerm, ty: &Ty) -> Ty {
    fn term_walk(c: u32, j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
        match tm {
            FOTerm::Var(i) => {
                if *i == j + c {
                    fo_term_shift(c as i32, 0, s)
                } else {
                    FOTerm::Var(*i)
                }
            }
            FOTerm::Const(k) => FOTerm::Const(*k),
            FOTerm::Func { sym, args } => FOTerm::Func {
                sym: *sym,
                args: args.iter().map(|a| term_walk(c, j, s, a)).collect(),
            },
        }
    }

    fn walk(c: u32, j: u32, s: &FOTerm, ty: &Ty) -> Ty {
        match ty {
            Ty::Atom(_) | Ty::Bot => ty.clone(),
            Ty::Pred { sym, args } => Ty::Pred {
                sym: *sym,
                args: args.iter().map(|a| term_walk(c, j, s, a)).collect(),
            },
            Ty::Arr(a, b) => Ty::Arr(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            Ty::Prod(a, b) => Ty::Prod(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            Ty::Sum(a, b) => Ty::Sum(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            Ty::Forall(body) => Ty::Forall(Box::new(walk(c + 1, j, s, body))),
            Ty::Exists(body) => Ty::Exists(Box::new(walk(c + 1, j, s, body))),
            Ty::Eq(lhs, rhs) => Ty::Eq(term_walk(c, j, s, lhs), term_walk(c, j, s, rhs)),
        }
    }

    walk(0, j, s, ty)
}

/// Top-level substitution: substitute term variable 0 with `s` in `body`, then shift down.
pub fn ty_term_subst_top(s: &FOTerm, body: &Ty) -> Ty {
    let su = fo_term_shift(1, 0, s);
    let sub = ty_term_subst(0, &su, body);
    ty_term_shift(-1, 0, &sub)
}

fn step_normal_order(tm: &Tm) -> Option<Tm> {
    match tm {
        Tm::App(f, x) => match f.as_ref() {
            Tm::Lam { body, .. } => Some(subst_top(x, body)),
            _ => {
                if let Some(next_f) = step_normal_order(f) {
                    Some(Tm::App(Box::new(next_f), x.clone()))
                } else {
                    step_normal_order(x).map(|next_x| Tm::App(f.clone(), Box::new(next_x)))
                }
            }
        },
        Tm::Lam { arg_ty, body } => step_normal_order(body).map(|next_body| Tm::Lam {
            arg_ty: arg_ty.clone(),
            body: Box::new(next_body),
        }),
        Tm::Pair(a, b) => {
            if let Some(next_a) = step_normal_order(a) {
                Some(Tm::Pair(Box::new(next_a), b.clone()))
            } else {
                step_normal_order(b).map(|next_b| Tm::Pair(a.clone(), Box::new(next_b)))
            }
        }
        Tm::Fst(t) => match t.as_ref() {
            Tm::Pair(a, _) => Some((**a).clone()),
            _ => step_normal_order(t).map(|next| Tm::Fst(Box::new(next))),
        },
        Tm::Snd(t) => match t.as_ref() {
            Tm::Pair(_, b) => Some((**b).clone()),
            _ => step_normal_order(t).map(|next| Tm::Snd(Box::new(next))),
        },
        Tm::Inl { rhs_ty, term } => step_normal_order(term).map(|next| Tm::Inl {
            rhs_ty: rhs_ty.clone(),
            term: Box::new(next),
        }),
        Tm::Inr { lhs_ty, term } => step_normal_order(term).map(|next| Tm::Inr {
            lhs_ty: lhs_ty.clone(),
            term: Box::new(next),
        }),
        Tm::Case { scrut, left, right } => match scrut.as_ref() {
            Tm::Inl { term, .. } => Some(subst_top(term, left)),
            Tm::Inr { term, .. } => Some(subst_top(term, right)),
            _ => {
                if let Some(next_scrut) = step_normal_order(scrut) {
                    Some(Tm::Case {
                        scrut: Box::new(next_scrut),
                        left: left.clone(),
                        right: right.clone(),
                    })
                } else if let Some(next_left) = step_normal_order(left) {
                    Some(Tm::Case {
                        scrut: scrut.clone(),
                        left: Box::new(next_left),
                        right: right.clone(),
                    })
                } else {
                    step_normal_order(right).map(|next_right| Tm::Case {
                        scrut: scrut.clone(),
                        left: left.clone(),
                        right: Box::new(next_right),
                    })
                }
            }
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => step_normal_order(bot_term).map(|next| Tm::Absurd {
            bot_term: Box::new(next),
            target_ty: target_ty.clone(),
        }),
        Tm::TLam { body } => step_normal_order(body).map(|next| Tm::TLam {
            body: Box::new(next),
        }),
        Tm::TApp { term, witness } => match term.as_ref() {
            Tm::TLam { body } => Some(tm_term_subst_top(witness, body)),
            _ => step_normal_order(term).map(|next| Tm::TApp {
                term: Box::new(next),
                witness: witness.clone(),
            }),
        },
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => step_normal_order(body).map(|next| Tm::Pack {
            witness: witness.clone(),
            body: Box::new(next),
            exists_ty: exists_ty.clone(),
        }),
        Tm::Unpack { scrut, body } => match scrut.as_ref() {
            Tm::Pack {
                witness,
                body: pack_body,
                ..
            } => Some(subst_top(pack_body, &tm_term_subst_top(witness, body))),
            _ => {
                if let Some(next_scrut) = step_normal_order(scrut) {
                    Some(Tm::Unpack {
                        scrut: Box::new(next_scrut),
                        body: body.clone(),
                    })
                } else {
                    step_normal_order(body).map(|next_body| Tm::Unpack {
                        scrut: scrut.clone(),
                        body: Box::new(next_body),
                    })
                }
            }
        },
        Tm::Refl { .. } => None,
        Tm::Subst {
            eq_proof,
            body,
            motive,
        } => match eq_proof.as_ref() {
            Tm::Refl { .. } => Some((**body).clone()),
            _ => step_normal_order(eq_proof)
                .map(|next| Tm::Subst {
                    eq_proof: Box::new(next),
                    body: body.clone(),
                    motive: motive.clone(),
                })
                .or_else(|| {
                    step_normal_order(body).map(|next| Tm::Subst {
                        eq_proof: eq_proof.clone(),
                        body: Box::new(next),
                        motive: motive.clone(),
                    })
                }),
        },
        Tm::Var(_) => None,
    }
}

pub fn normalize(tm: &Tm) -> Tm {
    normalize_with_limit(tm, 100_000).0
}

pub fn normalize_with_limit(tm: &Tm, max_steps: usize) -> (Tm, usize, bool) {
    let mut cur = tm.clone();
    let mut steps = 0usize;

    while steps < max_steps {
        match step_normal_order(&cur) {
            Some(next) => {
                cur = next;
                steps += 1;
            }
            None => return (cur, steps, false),
        }
    }

    (cur, steps, true)
}

/// ド・ブラウン・インデックス `var` が `tm` の中に自由出現するかを判定する
/// バインダを跨ぐたびに探す添字をインクリメント
pub fn free_in(var: u32, tm: &Tm) -> bool {
    match tm {
        Tm::Var(i) => *i == var,
        Tm::Lam { body, .. } => free_in(var + 1, body),
        Tm::App(f, x) | Tm::Pair(f, x) => free_in(var, f) || free_in(var, x),
        Tm::Fst(t) | Tm::Snd(t) => free_in(var, t),
        Tm::Inl { term, .. } | Tm::Inr { term, .. } => free_in(var, term),
        Tm::Case { scrut, left, right } => {
            free_in(var, scrut) || free_in(var + 1, left) || free_in(var + 1, right)
        }
        Tm::Absurd { bot_term, .. } => free_in(var, bot_term),
        Tm::TLam { body } => free_in(var, body),
        Tm::TApp { term, .. } => free_in(var, term),
        Tm::Pack { body, .. } => free_in(var, body),
        Tm::Unpack { scrut, body } => free_in(var, scrut) || free_in(var + 1, body),
        Tm::Refl { .. } => false,
        Tm::Subst { eq_proof, body, .. } => free_in(var, eq_proof) || free_in(var, body),
    }
}

/// ボトムアップ η 変換
///
/// - 関数 η: `λx:A. f x` → `f` (x ∉ FV(f))
/// - 直積 η: `⟨fst p, snd p⟩` → `p`
pub fn eta_reduce(tm: &Tm) -> Tm {
    match tm {
        Tm::Var(i) => Tm::Var(*i),

        Tm::Lam { arg_ty, body } => {
            let body_r = eta_reduce(body);
            // 関数 η: λx:A. f x → f when Var(0) ∉ FV(f)
            if let Tm::App(f, x) = &body_r
                && **x == Tm::Var(0)
                && !free_in(0, f)
            {
                return shift(-1, 0, f);
            }
            Tm::Lam {
                arg_ty: arg_ty.clone(),
                body: Box::new(body_r),
            }
        }

        Tm::App(f, x) => Tm::App(Box::new(eta_reduce(f)), Box::new(eta_reduce(x))),

        Tm::Pair(a, b) => {
            let a_r = eta_reduce(a);
            let b_r = eta_reduce(b);
            // 直積 η: ⟨fst p, snd p⟩ → p
            if let (Tm::Fst(pa), Tm::Snd(pb)) = (&a_r, &b_r)
                && **pa == **pb
            {
                return (**pa).clone();
            }
            Tm::Pair(Box::new(a_r), Box::new(b_r))
        }

        Tm::Fst(t) => Tm::Fst(Box::new(eta_reduce(t))),
        Tm::Snd(t) => Tm::Snd(Box::new(eta_reduce(t))),
        Tm::Inl { rhs_ty, term } => Tm::Inl {
            rhs_ty: rhs_ty.clone(),
            term: Box::new(eta_reduce(term)),
        },
        Tm::Inr { lhs_ty, term } => Tm::Inr {
            lhs_ty: lhs_ty.clone(),
            term: Box::new(eta_reduce(term)),
        },
        Tm::Case { scrut, left, right } => Tm::Case {
            scrut: Box::new(eta_reduce(scrut)),
            left: Box::new(eta_reduce(left)),
            right: Box::new(eta_reduce(right)),
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => Tm::Absurd {
            bot_term: Box::new(eta_reduce(bot_term)),
            target_ty: target_ty.clone(),
        },
        Tm::TLam { body } => Tm::TLam {
            body: Box::new(eta_reduce(body)),
        },
        Tm::TApp { term, witness } => Tm::TApp {
            term: Box::new(eta_reduce(term)),
            witness: witness.clone(),
        },
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => Tm::Pack {
            witness: witness.clone(),
            body: Box::new(eta_reduce(body)),
            exists_ty: exists_ty.clone(),
        },
        Tm::Unpack { scrut, body } => Tm::Unpack {
            scrut: Box::new(eta_reduce(scrut)),
            body: Box::new(eta_reduce(body)),
        },
        Tm::Refl { term } => Tm::Refl { term: term.clone() },
        Tm::Subst {
            eq_proof,
            body,
            motive,
        } => Tm::Subst {
            eq_proof: Box::new(eta_reduce(eq_proof)),
            body: Box::new(eta_reduce(body)),
            motive: motive.clone(),
        },
    }
}

/// β 正規化の後 η 変換を適用して βη 正規形を得る
pub fn normalize_eta(tm: &Tm) -> Tm {
    eta_reduce(&normalize(tm))
}

/// 二つの項が βη 同値かを判定する
/// 両者を βη 正規形に変換して構造比較する
pub fn tm_equiv(a: &Tm, b: &Tm) -> bool {
    normalize_eta(a) == normalize_eta(b)
}

pub fn tm_size(tm: &Tm) -> usize {
    match tm {
        Tm::Var(_) => 1,
        Tm::Lam { body, .. } => 1 + tm_size(body),
        Tm::App(f, x) => 1 + tm_size(f) + tm_size(x),
        Tm::Pair(a, b) => 1 + tm_size(a) + tm_size(b),
        Tm::Fst(t) | Tm::Snd(t) => 1 + tm_size(t),
        Tm::Inl { term, .. } | Tm::Inr { term, .. } => 1 + tm_size(term),
        Tm::Case { scrut, left, right } => 1 + tm_size(scrut) + tm_size(left) + tm_size(right),
        Tm::Absurd { bot_term, .. } => 1 + tm_size(bot_term),
        Tm::TLam { body } => 1 + tm_size(body),
        Tm::TApp { term, witness } => 1 + tm_size(term) + fo_term_size(witness),
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => 1 + fo_term_size(witness) + tm_size(body) + super::syntax::ty_size(exists_ty),
        Tm::Unpack { scrut, body } => 1 + tm_size(scrut) + tm_size(body),
        Tm::Refl { term } => 1 + fo_term_size(term),
        Tm::Subst { eq_proof, body, .. } => 1 + tm_size(eq_proof) + tm_size(body),
    }
}

pub fn tm_case_nodes(tm: &Tm) -> usize {
    match tm {
        Tm::Case { scrut, left, right } => {
            1 + tm_case_nodes(scrut) + tm_case_nodes(left) + tm_case_nodes(right)
        }
        Tm::Lam { body, .. } => tm_case_nodes(body),
        Tm::App(f, x) | Tm::Pair(f, x) => tm_case_nodes(f) + tm_case_nodes(x),
        Tm::Inl { term, .. } | Tm::Inr { term, .. } => tm_case_nodes(term),
        Tm::Fst(t) | Tm::Snd(t) => tm_case_nodes(t),
        Tm::Absurd { bot_term, .. } => tm_case_nodes(bot_term),
        Tm::TLam { body } => tm_case_nodes(body),
        Tm::TApp { term, .. } => tm_case_nodes(term),
        Tm::Pack { body, .. } => tm_case_nodes(body),
        Tm::Unpack { scrut, body } => tm_case_nodes(scrut) + tm_case_nodes(body),
        Tm::Refl { .. } => 0,
        Tm::Subst { eq_proof, body, .. } => tm_case_nodes(eq_proof) + tm_case_nodes(body),
        Tm::Var(_) => 0,
    }
}

pub fn tm_repeat_case_nodes(tm: &Tm) -> usize {
    fn go(tm: &Tm, ancestors: &mut Vec<Tm>) -> usize {
        match tm {
            Tm::Case { scrut, left, right } => {
                let repeat = ancestors.iter().any(|s| s == scrut.as_ref()) as usize;
                ancestors.push((**scrut).clone());
                let l = go(left, ancestors);
                let r = go(right, ancestors);
                ancestors.pop();
                repeat + l + r
            }
            Tm::Lam { body, .. } => go(body, ancestors),
            Tm::App(f, x) | Tm::Pair(f, x) => go(f, ancestors) + go(x, ancestors),
            Tm::Inl { term, .. } | Tm::Inr { term, .. } => go(term, ancestors),
            Tm::Fst(t) | Tm::Snd(t) => go(t, ancestors),
            Tm::Absurd { bot_term, .. } => go(bot_term, ancestors),
            Tm::TLam { body } => go(body, ancestors),
            Tm::TApp { term, .. } => go(term, ancestors),
            Tm::Pack { body, .. } => go(body, ancestors),
            Tm::Unpack { scrut, body } => go(scrut, ancestors) + go(body, ancestors),
            Tm::Refl { .. } => 0,
            Tm::Subst { eq_proof, body, .. } => go(eq_proof, ancestors) + go(body, ancestors),
            Tm::Var(_) => 0,
        }
    }
    let mut anc = Vec::new();
    go(tm, &mut anc)
}

// --- Term-variable operations on proof terms (2-sort shift/subst) ---

/// Shift term variables inside a proof term by `d`, with cutoff `cutoff`.
/// TLam and Unpack bind term variables, so cutoff increments under them.
pub fn tm_term_shift(d: i32, cutoff: u32, tm: &Tm) -> Tm {
    match tm {
        Tm::Var(_) => tm.clone(),
        Tm::Lam { arg_ty, body } => Tm::Lam {
            arg_ty: ty_term_shift(d, cutoff, arg_ty),
            body: Box::new(tm_term_shift(d, cutoff, body)),
        },
        Tm::App(f, x) => Tm::App(
            Box::new(tm_term_shift(d, cutoff, f)),
            Box::new(tm_term_shift(d, cutoff, x)),
        ),
        Tm::Pair(a, b) => Tm::Pair(
            Box::new(tm_term_shift(d, cutoff, a)),
            Box::new(tm_term_shift(d, cutoff, b)),
        ),
        Tm::Fst(t) => Tm::Fst(Box::new(tm_term_shift(d, cutoff, t))),
        Tm::Snd(t) => Tm::Snd(Box::new(tm_term_shift(d, cutoff, t))),
        Tm::Inl { rhs_ty, term } => Tm::Inl {
            rhs_ty: ty_term_shift(d, cutoff, rhs_ty),
            term: Box::new(tm_term_shift(d, cutoff, term)),
        },
        Tm::Inr { lhs_ty, term } => Tm::Inr {
            lhs_ty: ty_term_shift(d, cutoff, lhs_ty),
            term: Box::new(tm_term_shift(d, cutoff, term)),
        },
        Tm::Case { scrut, left, right } => Tm::Case {
            scrut: Box::new(tm_term_shift(d, cutoff, scrut)),
            left: Box::new(tm_term_shift(d, cutoff, left)),
            right: Box::new(tm_term_shift(d, cutoff, right)),
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => Tm::Absurd {
            bot_term: Box::new(tm_term_shift(d, cutoff, bot_term)),
            target_ty: ty_term_shift(d, cutoff, target_ty),
        },
        Tm::TLam { body } => Tm::TLam {
            body: Box::new(tm_term_shift(d, cutoff + 1, body)),
        },
        Tm::TApp { term, witness } => Tm::TApp {
            term: Box::new(tm_term_shift(d, cutoff, term)),
            witness: fo_term_shift(d, cutoff, witness),
        },
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => Tm::Pack {
            witness: fo_term_shift(d, cutoff, witness),
            body: Box::new(tm_term_shift(d, cutoff, body)),
            exists_ty: ty_term_shift(d, cutoff, exists_ty),
        },
        Tm::Unpack { scrut, body } => Tm::Unpack {
            scrut: Box::new(tm_term_shift(d, cutoff, scrut)),
            body: Box::new(tm_term_shift(d, cutoff + 1, body)),
        },
        Tm::Refl { term } => Tm::Refl {
            term: fo_term_shift(d, cutoff, term),
        },
        Tm::Subst {
            eq_proof,
            body,
            motive,
        } => Tm::Subst {
            eq_proof: Box::new(tm_term_shift(d, cutoff, eq_proof)),
            body: Box::new(tm_term_shift(d, cutoff, body)),
            motive: ty_term_shift(d, cutoff, motive),
        },
    }
}

/// Substitute term variable `j` with FOTerm `s` in a proof term.
pub fn tm_term_subst(j: u32, s: &FOTerm, tm: &Tm) -> Tm {
    fn ty_at(c: u32, j: u32, s: &FOTerm, ty: &Ty) -> Ty {
        ty_term_subst(j + c, &fo_term_shift(c as i32, 0, s), ty)
    }

    fn fo_at(c: u32, j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
        fo_term_subst(j + c, &fo_term_shift(c as i32, 0, s), tm)
    }

    fn walk(c: u32, j: u32, s: &FOTerm, tm: &Tm) -> Tm {
        match tm {
            Tm::Var(_) => tm.clone(),
            Tm::Lam { arg_ty, body } => Tm::Lam {
                arg_ty: ty_at(c, j, s, arg_ty),
                body: Box::new(walk(c, j, s, body)),
            },
            Tm::App(f, x) => Tm::App(Box::new(walk(c, j, s, f)), Box::new(walk(c, j, s, x))),
            Tm::Pair(a, b) => Tm::Pair(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            Tm::Fst(t) => Tm::Fst(Box::new(walk(c, j, s, t))),
            Tm::Snd(t) => Tm::Snd(Box::new(walk(c, j, s, t))),
            Tm::Inl { rhs_ty, term } => Tm::Inl {
                rhs_ty: ty_at(c, j, s, rhs_ty),
                term: Box::new(walk(c, j, s, term)),
            },
            Tm::Inr { lhs_ty, term } => Tm::Inr {
                lhs_ty: ty_at(c, j, s, lhs_ty),
                term: Box::new(walk(c, j, s, term)),
            },
            Tm::Case { scrut, left, right } => Tm::Case {
                scrut: Box::new(walk(c, j, s, scrut)),
                left: Box::new(walk(c, j, s, left)),
                right: Box::new(walk(c, j, s, right)),
            },
            Tm::Absurd {
                bot_term,
                target_ty,
            } => Tm::Absurd {
                bot_term: Box::new(walk(c, j, s, bot_term)),
                target_ty: ty_at(c, j, s, target_ty),
            },
            Tm::TLam { body } => Tm::TLam {
                body: Box::new(walk(c + 1, j, s, body)),
            },
            Tm::TApp { term, witness } => Tm::TApp {
                term: Box::new(walk(c, j, s, term)),
                witness: fo_at(c, j, s, witness),
            },
            Tm::Pack {
                witness,
                body,
                exists_ty,
            } => Tm::Pack {
                witness: fo_at(c, j, s, witness),
                body: Box::new(walk(c, j, s, body)),
                exists_ty: ty_at(c, j, s, exists_ty),
            },
            Tm::Unpack { scrut, body } => Tm::Unpack {
                scrut: Box::new(walk(c, j, s, scrut)),
                body: Box::new(walk(c + 1, j, s, body)),
            },
            Tm::Refl { term } => Tm::Refl {
                term: fo_at(c, j, s, term),
            },
            Tm::Subst {
                eq_proof,
                body,
                motive,
            } => Tm::Subst {
                eq_proof: Box::new(walk(c, j, s, eq_proof)),
                body: Box::new(walk(c, j, s, body)),
                motive: ty_at(c, j, s, motive),
            },
        }
    }

    walk(0, j, s, tm)
}

/// Top-level term-variable substitution: substitute term var 0 with `s` in `body`, then shift down.
pub fn tm_term_subst_top(s: &FOTerm, body: &Tm) -> Tm {
    let su = fo_term_shift(1, 0, s);
    let sub = tm_term_subst(0, &su, body);
    tm_term_shift(-1, 0, &sub)
}

/// Check if term variable `var` is free in a type.
pub fn ty_term_free_in(var: u32, ty: &Ty) -> bool {
    match ty {
        Ty::Atom(_) | Ty::Bot => false,
        Ty::Pred { args, .. } => args.iter().any(|a| fo_term_free_in(var, a)),
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            ty_term_free_in(var, a) || ty_term_free_in(var, b)
        }
        Ty::Forall(body) | Ty::Exists(body) => ty_term_free_in(var + 1, body),
        Ty::Eq(s, t) => fo_term_free_in(var, s) || fo_term_free_in(var, t),
    }
}

/// Check if term variable `var` is free in an FOTerm.
pub fn fo_term_free_in(var: u32, tm: &FOTerm) -> bool {
    match tm {
        FOTerm::Var(i) => *i == var,
        FOTerm::Const(_) => false,
        FOTerm::Func { args, .. } => args.iter().any(|a| fo_term_free_in(var, a)),
    }
}
