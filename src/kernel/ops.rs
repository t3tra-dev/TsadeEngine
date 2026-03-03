use super::Tm;

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
        }
    }

    walk(0, j, s, tm)
}

pub fn subst_top(s: &Tm, body: &Tm) -> Tm {
    let s_up = shift(1, 0, s);
    let body_sub = subst(0, &s_up, body);
    shift(-1, 0, &body_sub)
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
            Tm::Var(_) => 0,
        }
    }
    let mut anc = Vec::new();
    go(tm, &mut anc)
}
