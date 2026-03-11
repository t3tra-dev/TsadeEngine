use super::{PTm, SearchState};
use crate::kernel::Tm;

pub fn try_finalize(state: &SearchState) -> Option<Tm> {
    if !state.goals.is_empty() {
        return None;
    }
    fn conv(tm: &PTm) -> Option<Tm> {
        match tm {
            PTm::Hole { .. } => None,
            PTm::Var(i) => Some(Tm::Var(*i)),
            PTm::Lam { arg_ty, body } => Some(Tm::Lam {
                arg_ty: arg_ty.clone(),
                body: Box::new(conv(body)?),
            }),
            PTm::App(f, x) => Some(Tm::App(Box::new(conv(f)?), Box::new(conv(x)?))),
            PTm::Pair(a, b) => Some(Tm::Pair(Box::new(conv(a)?), Box::new(conv(b)?))),
            PTm::Inl { rhs_ty, term } => Some(Tm::Inl {
                rhs_ty: rhs_ty.clone(),
                term: Box::new(conv(term)?),
            }),
            PTm::Inr { lhs_ty, term } => Some(Tm::Inr {
                lhs_ty: lhs_ty.clone(),
                term: Box::new(conv(term)?),
            }),
            PTm::Case { scrut, left, right } => Some(Tm::Case {
                scrut: Box::new(conv(scrut)?),
                left: Box::new(conv(left)?),
                right: Box::new(conv(right)?),
            }),
            PTm::Fst(t) => Some(Tm::Fst(Box::new(conv(t)?))),
            PTm::Snd(t) => Some(Tm::Snd(Box::new(conv(t)?))),
            PTm::Absurd {
                bot_term,
                target_ty,
            } => Some(Tm::Absurd {
                bot_term: Box::new(conv(bot_term)?),
                target_ty: target_ty.clone(),
            }),
            PTm::TLam { body } => Some(Tm::TLam {
                body: Box::new(conv(body)?),
            }),
            PTm::TApp { term, witness } => Some(Tm::TApp {
                term: Box::new(conv(term)?),
                witness: witness.clone(),
            }),
            PTm::Pack {
                witness,
                body,
                exists_ty,
            } => Some(Tm::Pack {
                witness: witness.clone(),
                body: Box::new(conv(body)?),
                exists_ty: exists_ty.clone(),
            }),
            PTm::Unpack { scrut, body } => Some(Tm::Unpack {
                scrut: Box::new(conv(scrut)?),
                body: Box::new(conv(body)?),
            }),
            PTm::Refl { term } => Some(Tm::Refl { term: term.clone() }),
            PTm::Subst {
                eq_proof,
                body,
                motive,
            } => Some(Tm::Subst {
                eq_proof: Box::new(conv(eq_proof)?),
                body: Box::new(conv(body)?),
                motive: motive.clone(),
            }),
        }
    }
    conv(&state.root)
}
