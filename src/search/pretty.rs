use crate::kernel::{Tm, Ty};

use super::PTm;

pub fn pretty_ty(ty: &Ty) -> String {
    fn go(ty: &Ty, p: u8) -> String {
        match ty {
            Ty::Atom(i) => format!("A{i}"),
            Ty::Bot => "Bot".to_string(),
            Ty::Prod(a, b) => {
                let s = format!("{} * {}", go(a, 2), go(b, 2));
                if p > 2 { format!("({s})") } else { s }
            }
            Ty::Sum(a, b) => {
                let s = format!("{} + {}", go(a, 1), go(b, 1));
                if p > 1 { format!("({s})") } else { s }
            }
            Ty::Arr(a, b) => {
                let s = format!("{} -> {}", go(a, 2), go(b, 0));
                if p > 0 { format!("({s})") } else { s }
            }
        }
    }
    go(ty, 0)
}

fn var_name(depth: usize, i: u32) -> String {
    let idx = i as usize;
    if idx < depth {
        format!("x{}", depth - 1 - idx)
    } else {
        format!("v{i}")
    }
}

pub fn pretty_tm(tm: &Tm) -> String {
    fn go(tm: &Tm, depth: usize, p: u8) -> String {
        match tm {
            Tm::Var(i) => var_name(depth, *i),
            Tm::Lam { arg_ty, body } => {
                let name = format!("x{depth}");
                let s = format!("\\{name}:{}. {}", pretty_ty(arg_ty), go(body, depth + 1, 0));
                if p > 0 { format!("({s})") } else { s }
            }
            Tm::App(f, x) => {
                let s = format!("{} {}", go(f, depth, 1), go(x, depth, 2));
                if p > 1 { format!("({s})") } else { s }
            }
            Tm::Pair(a, b) => format!("<{}, {}>", go(a, depth, 0), go(b, depth, 0)),
            Tm::Inl { rhs_ty, term } => {
                format!("inl {} : +{}", go(term, depth, 2), pretty_ty(rhs_ty))
            }
            Tm::Inr { lhs_ty, term } => {
                format!("inr {} : {}+", go(term, depth, 2), pretty_ty(lhs_ty))
            }
            Tm::Case { scrut, left, right } => format!(
                "case {} of L=>{} | R=>{}",
                go(scrut, depth, 2),
                go(left, depth + 1, 0),
                go(right, depth + 1, 0)
            ),
            Tm::Fst(t) => format!("fst {}", go(t, depth, 2)),
            Tm::Snd(t) => format!("snd {}", go(t, depth, 2)),
            Tm::Absurd {
                bot_term,
                target_ty,
            } => format!(
                "absurd {} as {}",
                go(bot_term, depth, 2),
                pretty_ty(target_ty)
            ),
        }
    }
    go(tm, 0, 0)
}

pub fn pretty_ptm(tm: &PTm) -> String {
    fn go(tm: &PTm, depth: usize, p: u8) -> String {
        match tm {
            PTm::Hole { id, ty } => format!("?{id}:{}", pretty_ty(ty)),
            PTm::Var(i) => var_name(depth, *i),
            PTm::Lam { arg_ty, body } => {
                let name = format!("x{depth}");
                let s = format!("\\{name}:{}. {}", pretty_ty(arg_ty), go(body, depth + 1, 0));
                if p > 0 { format!("({s})") } else { s }
            }
            PTm::App(f, x) => {
                let s = format!("{} {}", go(f, depth, 1), go(x, depth, 2));
                if p > 1 { format!("({s})") } else { s }
            }
            PTm::Pair(a, b) => format!("<{}, {}>", go(a, depth, 0), go(b, depth, 0)),
            PTm::Inl { rhs_ty, term } => {
                format!("inl {} : +{}", go(term, depth, 2), pretty_ty(rhs_ty))
            }
            PTm::Inr { lhs_ty, term } => {
                format!("inr {} : {}+", go(term, depth, 2), pretty_ty(lhs_ty))
            }
            PTm::Case { scrut, left, right } => format!(
                "case {} of L=>{} | R=>{}",
                go(scrut, depth, 2),
                go(left, depth + 1, 0),
                go(right, depth + 1, 0)
            ),
            PTm::Fst(t) => format!("fst {}", go(t, depth, 2)),
            PTm::Snd(t) => format!("snd {}", go(t, depth, 2)),
            PTm::Absurd {
                bot_term,
                target_ty,
            } => format!(
                "absurd {} as {}",
                go(bot_term, depth, 2),
                pretty_ty(target_ty)
            ),
        }
    }
    go(tm, 0, 0)
}

// Unicode ベースの人間に読みやすい表記
pub fn pretty_ty_unicode(ty: &Ty) -> String {
    fn go(ty: &Ty, p: u8) -> String {
        match ty {
            Ty::Atom(i) => format!("A{i}"),
            Ty::Bot => "⊥".to_string(),
            Ty::Prod(a, b) => {
                let s = format!("{} ∧ {}", go(a, 2), go(b, 2));
                if p > 2 { format!("({s})") } else { s }
            }
            Ty::Sum(a, b) => {
                let s = format!("{} ∨ {}", go(a, 1), go(b, 1));
                if p > 1 { format!("({s})") } else { s }
            }
            Ty::Arr(a, b) => {
                let s = format!("{} → {}", go(a, 2), go(b, 0));
                if p > 0 { format!("({s})") } else { s }
            }
        }
    }
    go(ty, 0)
}

pub fn pretty_tm_unicode(tm: &Tm) -> String {
    fn go(tm: &Tm, depth: usize, p: u8) -> String {
        match tm {
            Tm::Var(i) => var_name(depth, *i),
            Tm::Lam { arg_ty, body } => {
                let name = format!("x{depth}");
                let s = format!(
                    "λ{}:{}. {}",
                    name,
                    pretty_ty_unicode(arg_ty),
                    go(body, depth + 1, 0)
                );
                if p > 0 { format!("({s})") } else { s }
            }
            Tm::App(f, x) => {
                let s = format!("{} {}", go(f, depth, 1), go(x, depth, 2));
                if p > 1 { format!("({s})") } else { s }
            }
            Tm::Pair(a, b) => format!("⟨{}, {}⟩", go(a, depth, 0), go(b, depth, 0)),
            Tm::Inl { rhs_ty, term } => {
                format!(
                    "inl {} : ∨{}",
                    go(term, depth, 2),
                    pretty_ty_unicode(rhs_ty)
                )
            }
            Tm::Inr { lhs_ty, term } => {
                format!(
                    "inr {} : {}∨",
                    go(term, depth, 2),
                    pretty_ty_unicode(lhs_ty)
                )
            }
            Tm::Case { scrut, left, right } => format!(
                "case {} of\n  | left  ⇒ {}\n  | right ⇒ {}",
                go(scrut, depth, 2),
                go(left, depth + 1, 0),
                go(right, depth + 1, 0)
            ),
            Tm::Fst(t) => format!("π₁({})", go(t, depth, 2)),
            Tm::Snd(t) => format!("π₂({})", go(t, depth, 2)),
            Tm::Absurd {
                bot_term,
                target_ty,
            } => format!(
                "absurd {} : {}",
                go(bot_term, depth, 2),
                pretty_ty_unicode(target_ty)
            ),
        }
    }
    go(tm, 0, 0)
}

pub fn pretty_ptm_unicode(tm: &PTm) -> String {
    fn go(tm: &PTm, depth: usize, p: u8) -> String {
        match tm {
            PTm::Hole { id, ty } => format!("?{id}:{}", pretty_ty_unicode(ty)),
            PTm::Var(i) => var_name(depth, *i),
            PTm::Lam { arg_ty, body } => {
                let name = format!("x{depth}");
                let s = format!(
                    "λ{}:{}. {}",
                    name,
                    pretty_ty_unicode(arg_ty),
                    go(body, depth + 1, 0)
                );
                if p > 0 { format!("({s})") } else { s }
            }
            PTm::App(f, x) => {
                let s = format!("{} {}", go(f, depth, 1), go(x, depth, 2));
                if p > 1 { format!("({s})") } else { s }
            }
            PTm::Pair(a, b) => format!("⟨{}, {}⟩", go(a, depth, 0), go(b, depth, 0)),
            PTm::Inl { rhs_ty, term } => {
                format!(
                    "inl {} : ∨{}",
                    go(term, depth, 2),
                    pretty_ty_unicode(rhs_ty)
                )
            }
            PTm::Inr { lhs_ty, term } => {
                format!(
                    "inr {} : {}∨",
                    go(term, depth, 2),
                    pretty_ty_unicode(lhs_ty)
                )
            }
            PTm::Case { scrut, left, right } => format!(
                "case {} of\n  | left  ⇒ {}\n  | right ⇒ {}",
                go(scrut, depth, 2),
                go(left, depth + 1, 0),
                go(right, depth + 1, 0)
            ),
            PTm::Fst(t) => format!("π₁({})", go(t, depth, 2)),
            PTm::Snd(t) => format!("π₂({})", go(t, depth, 2)),
            PTm::Absurd {
                bot_term,
                target_ty,
            } => format!(
                "absurd {} : {}",
                go(bot_term, depth, 2),
                pretty_ty_unicode(target_ty)
            ),
        }
    }
    go(tm, 0, 0)
}
