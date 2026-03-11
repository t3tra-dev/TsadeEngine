mod logic;
mod ops;
mod syntax;
mod typing;

pub use logic::{KripkeCounterModel, find_kripke_countermodel, is_intuitionistic_theorem};
pub use ops::{
    eta_reduce, fo_term_shift, fo_term_subst, fo_term_subst_top, free_in, normalize, normalize_eta,
    normalize_with_limit, shift, subst, subst_top, tm_case_nodes, tm_equiv, tm_repeat_case_nodes,
    tm_size, tm_term_shift, tm_term_subst, tm_term_subst_top, ty_term_free_in, ty_term_shift,
    ty_term_subst, ty_term_subst_top,
};
pub use syntax::{Ctx, FOTerm, Tm, Ty, fo_term_size, ty_size};
pub use typing::{TypeError, check, ctx_lookup, infer, normalize_ty, ty_equiv};

#[cfg(test)]
mod tests;
