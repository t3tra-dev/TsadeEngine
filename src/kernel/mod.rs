mod logic;
mod ops;
mod syntax;
mod typing;

pub use logic::{KripkeCounterModel, find_kripke_countermodel, is_intuitionistic_theorem};
pub use ops::{
    normalize, normalize_with_limit, shift, subst, subst_top, tm_case_nodes, tm_repeat_case_nodes,
    tm_size,
};
pub use syntax::{Ctx, Tm, Ty, ty_size};
pub use typing::{TypeError, check, ctx_lookup, infer};

#[cfg(test)]
mod tests;
