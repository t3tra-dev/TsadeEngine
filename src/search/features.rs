use super::{PTm, PartialFeatures, SearchState};
use crate::kernel::ty_size;

fn count_nodes(tm: &PTm, mut pred: impl FnMut(&PTm) -> usize + Copy) -> usize {
    fn go(tm: &PTm, pred: &mut impl FnMut(&PTm) -> usize) -> usize {
        let here = pred(tm);
        here + match tm {
            PTm::Hole { .. } | PTm::Var(_) => 0,
            PTm::Lam { body, .. } => go(body, pred),
            PTm::App(f, x) | PTm::Pair(f, x) => go(f, pred) + go(x, pred),
            PTm::Inl { term, .. } | PTm::Inr { term, .. } => go(term, pred),
            PTm::Case { scrut, left, right } => go(scrut, pred) + go(left, pred) + go(right, pred),
            PTm::Fst(t) | PTm::Snd(t) => go(t, pred),
            PTm::Absurd { bot_term, .. } => go(bot_term, pred),
        }
    }
    go(tm, &mut pred)
}

pub fn ptm_size(tm: &PTm) -> usize {
    count_nodes(tm, |_| 1)
}

pub fn ptm_app_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::App(_, _))))
}

pub fn ptm_case_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::Case { .. })))
}

pub fn ptm_pair_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::Pair(_, _))))
}

pub fn ptm_sum_intro_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| {
        usize::from(matches!(n, PTm::Inl { .. } | PTm::Inr { .. }))
    })
}

pub fn ptm_proj_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::Fst(_) | PTm::Snd(_))))
}

pub fn ptm_repeat_case_nodes(tm: &PTm) -> usize {
    fn go(tm: &PTm, ancestors: &mut Vec<u64>, binders: u32) -> usize {
        match tm {
            PTm::Case { scrut, left, right } => {
                let fp = super::engine::scrutinee_fingerprint(scrut, binders);
                let repeat = usize::from(ancestors.contains(&fp));
                ancestors.push(fp);
                let l = go(left, ancestors, binders + 1);
                let r = go(right, ancestors, binders + 1);
                ancestors.pop();
                repeat + l + r
            }
            PTm::Lam { body, .. } => go(body, ancestors, binders + 1),
            PTm::App(f, x) | PTm::Pair(f, x) => {
                go(f, ancestors, binders) + go(x, ancestors, binders)
            }
            PTm::Inl { term, .. } | PTm::Inr { term, .. } => go(term, ancestors, binders),
            PTm::Fst(t) | PTm::Snd(t) => go(t, ancestors, binders),
            PTm::Absurd { bot_term, .. } => go(bot_term, ancestors, binders),
            PTm::Hole { .. } | PTm::Var(_) => 0,
        }
    }
    let mut anc = Vec::new();
    go(tm, &mut anc, 0)
}

pub fn partial_features(state: &SearchState) -> PartialFeatures {
    PartialFeatures {
        holes: state.goals.len(),
        goal_complexity: state.goals.values().map(|g| ty_size(&g.ty)).sum(),
        root_size: ptm_size(&state.root),
        app_nodes: ptm_app_nodes(&state.root),
        case_nodes: ptm_case_nodes(&state.root),
        repeat_case_nodes: ptm_repeat_case_nodes(&state.root),
        pair_nodes: ptm_pair_nodes(&state.root),
        sum_intro_nodes: ptm_sum_intro_nodes(&state.root),
        proj_nodes: ptm_proj_nodes(&state.root),
    }
}

pub fn score_partial(state: &SearchState) -> i64 {
    let f = partial_features(state);
    if f.holes == 0 {
        return 1_000_000
            - (f.root_size as i64)
            - (f.app_nodes as i64 * 2)
            - (f.case_nodes as i64 * 4)
            - (f.repeat_case_nodes as i64 * 20);
    }
    let holes = f.holes as i64;
    let goal_c = f.goal_complexity as i64;
    let close_bonus = 3000 / (holes + 1) + 1200 / (goal_c + 1);
    let intro_progress = (f.pair_nodes.min(4) as i64) * 30
        + (f.sum_intro_nodes.min(4) as i64) * 40
        + (f.proj_nodes.min(6) as i64) * 20;
    -((holes) * 1800
        + (holes * holes) * 220
        + (goal_c) * 55
        + (f.root_size as i64) * 3
        + (f.app_nodes as i64) * 10
        + (f.case_nodes as i64) * 8
        + (f.repeat_case_nodes as i64) * 30)
        + intro_progress
        + close_bonus
}
