use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::kernel::{Ctx, Tm, Ty};

pub trait ChoiceStream {
    fn next_u32(&mut self) -> u32;
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PTm {
    Hole {
        id: u32,
        ty: Ty,
    },
    Var(u32),
    Lam {
        arg_ty: Ty,
        body: Box<PTm>,
    },
    App(Box<PTm>, Box<PTm>),
    Pair(Box<PTm>, Box<PTm>),
    Inl {
        rhs_ty: Ty,
        term: Box<PTm>,
    },
    Inr {
        lhs_ty: Ty,
        term: Box<PTm>,
    },
    Case {
        scrut: Box<PTm>,
        left: Box<PTm>,
        right: Box<PTm>,
    },
    Fst(Box<PTm>),
    Snd(Box<PTm>),
    Absurd {
        bot_term: Box<PTm>,
        target_ty: Ty,
    },
}

#[derive(Clone, Debug)]
pub struct Goal {
    pub id: u32,
    pub ctx: Ctx,
    pub ty: Ty,
    pub allow_case: bool,
}

#[derive(Clone, Debug)]
pub struct SearchState {
    pub root: PTm,
    pub goals: HashMap<u32, Goal>,
    pub next_hole_id: u32,
}

impl SearchState {
    pub fn new(ctx: &Ctx, ty: &Ty) -> Self {
        let mut goals = HashMap::new();
        goals.insert(
            0,
            Goal {
                id: 0,
                ctx: ctx.clone(),
                ty: ty.clone(),
                allow_case: true,
            },
        );
        Self {
            root: PTm::Hole {
                id: 0,
                ty: ty.clone(),
            },
            goals,
            next_hole_id: 1,
        }
    }

    pub(crate) fn fresh_hole(&mut self, ctx: Ctx, ty: Ty, allow_case: bool) -> PTm {
        let id = self.next_hole_id;
        self.next_hole_id += 1;
        self.goals.insert(
            id,
            Goal {
                id,
                ctx,
                ty: ty.clone(),
                allow_case,
            },
        );
        PTm::Hole { id, ty }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum GoalStrategy {
    Shallow,
    Deep,
    Random,
}

#[derive(Clone, Debug)]
pub struct SearchPolicy {
    pub w_var: u32,
    pub w_app: u32,
    pub w_direct_app: u32,
    pub w_hole: u32,
    pub w_pair: u32,
    pub w_proj: u32,
    pub w_sum_intro: u32,
    pub w_case: u32,
    pub w_absurd: u32,
    pub branch_budget_scale_per_mille: u32,
    pub goal_strategy: GoalStrategy,
}

impl SearchPolicy {
    pub(crate) fn signature(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        // メモ再利用を優先して、重みは粗いバケットに落とす
        (self.w_var / 4).hash(&mut h);
        (self.w_app / 4).hash(&mut h);
        (self.w_direct_app / 4).hash(&mut h);
        (self.w_hole / 4).hash(&mut h);
        (self.w_pair / 4).hash(&mut h);
        (self.w_proj / 4).hash(&mut h);
        (self.w_sum_intro / 4).hash(&mut h);
        (self.w_case / 4).hash(&mut h);
        (self.w_absurd / 4).hash(&mut h);
        (self.branch_budget_scale_per_mille / 100).hash(&mut h);
        (self.goal_strategy as u8).hash(&mut h);
        h.finish()
    }
}

impl Default for SearchPolicy {
    fn default() -> Self {
        Self {
            w_var: 8,
            w_app: 3,
            w_direct_app: 6,
            w_hole: 1,
            w_pair: 6,
            w_proj: 2,
            w_sum_intro: 4,
            w_case: 2,
            w_absurd: 2,
            branch_budget_scale_per_mille: 750,
            goal_strategy: GoalStrategy::Shallow,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SearchConfig {
    pub beam_width: usize,
    pub max_iters: usize,
    pub expand_per_state: usize,
    pub synth_budget: u32,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            beam_width: 20,
            max_iters: 200,
            expand_per_state: 3,
            synth_budget: 10,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SearchMetrics {
    pub iterations: usize,
    pub expanded_states: usize,
    pub min_holes: usize,
    pub min_goal_complexity: usize,
    pub min_root_size: usize,
    pub min_app_nodes: usize,
    pub min_case_nodes: usize,
    pub min_repeat_case_nodes: usize,
    pub max_pair_nodes_seen: usize,
    pub max_sum_intro_nodes_seen: usize,
    pub max_proj_nodes_seen: usize,
    pub dedup_dropped: usize,
    pub memo_hits: usize,
    pub repair_invocations: usize,
    pub repair_goal_attempts: usize,
    pub repair_candidates_tried: usize,
    pub repair_success_steps: usize,
    pub repair_promoted_states: usize,
}

impl SearchMetrics {
    pub(crate) fn observe_state(&mut self, state: &SearchState) {
        let feat = super::partial_features(state);
        if self.iterations == 0 && self.expanded_states == 0 {
            self.min_holes = feat.holes;
            self.min_goal_complexity = feat.goal_complexity;
            self.min_root_size = feat.root_size;
            self.min_app_nodes = feat.app_nodes;
            self.min_case_nodes = feat.case_nodes;
            self.min_repeat_case_nodes = feat.repeat_case_nodes;
            self.max_pair_nodes_seen = feat.pair_nodes;
            self.max_sum_intro_nodes_seen = feat.sum_intro_nodes;
            self.max_proj_nodes_seen = feat.proj_nodes;
            return;
        }
        self.min_holes = self.min_holes.min(feat.holes);
        self.min_goal_complexity = self.min_goal_complexity.min(feat.goal_complexity);
        self.min_root_size = self.min_root_size.min(feat.root_size);
        self.min_app_nodes = self.min_app_nodes.min(feat.app_nodes);
        self.min_case_nodes = self.min_case_nodes.min(feat.case_nodes);
        self.min_repeat_case_nodes = self.min_repeat_case_nodes.min(feat.repeat_case_nodes);
        self.max_pair_nodes_seen = self.max_pair_nodes_seen.max(feat.pair_nodes);
        self.max_sum_intro_nodes_seen = self.max_sum_intro_nodes_seen.max(feat.sum_intro_nodes);
        self.max_proj_nodes_seen = self.max_proj_nodes_seen.max(feat.proj_nodes);
    }
}

#[derive(Clone, Debug)]
pub struct SearchOutcome {
    pub best_state: SearchState,
    pub best_score: i64,
    pub complete_term: Option<Tm>,
    pub metrics: SearchMetrics,
}

#[derive(Clone, Copy, Debug)]
pub struct PartialFeatures {
    pub holes: usize,
    pub goal_complexity: usize,
    pub root_size: usize,
    pub app_nodes: usize,
    pub case_nodes: usize,
    pub repeat_case_nodes: usize,
    pub pair_nodes: usize,
    pub sum_intro_nodes: usize,
    pub proj_nodes: usize,
}
