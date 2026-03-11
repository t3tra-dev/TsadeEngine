mod engine;
mod features;
mod finalize;
mod pretty;
mod types;
pub mod visualize;

pub use engine::beam_search;
pub use features::{
    partial_features, ptm_app_nodes, ptm_case_nodes, ptm_pair_nodes, ptm_proj_nodes,
    ptm_repeat_case_nodes, ptm_size, ptm_sum_intro_nodes, score_partial,
};
pub use finalize::try_finalize;
pub use pretty::{
    pretty_fo_term, pretty_ptm, pretty_ptm_unicode, pretty_tm, pretty_tm_unicode, pretty_ty,
    pretty_ty_unicode,
};
pub use types::{
    ChoiceStream, Goal, GoalStrategy, PTm, PartialFeatures, SearchConfig, SearchMetrics,
    SearchOutcome, SearchPolicy, SearchState,
};

#[cfg(test)]
mod tests;
