use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::kernel::ty_size;
use crate::kernel::{Ctx, Tm, Ty};

use super::super::{
    ChoiceStream, Goal, GoalStrategy, PTm, SearchConfig, SearchMetrics, SearchOutcome,
    SearchPolicy, SearchState, score_partial, try_finalize,
};
use super::synth::{SearchRuntime, ctx_fingerprint, greedy_local_repair, replace_hole, synth};

fn select_goal_id(
    state: &SearchState,
    choices: &mut impl ChoiceStream,
    strategy: GoalStrategy,
) -> Option<u32> {
    if state.goals.is_empty() {
        return None;
    }
    let mut goals: Vec<&Goal> = state.goals.values().collect();
    match strategy {
        GoalStrategy::Random => {
            let idx = (choices.next_u32() as usize) % goals.len();
            Some(goals[idx].id)
        }
        GoalStrategy::Shallow => {
            goals.sort_by_key(|g| {
                let atom_prio = if matches!(g.ty, Ty::Atom(_)) { 0 } else { 1 };
                (atom_prio, ty_size(&g.ty), g.id as usize)
            });
            Some(goals[0].id)
        }
        GoalStrategy::Deep => {
            goals.sort_by_key(|g| {
                let atom_prio = if matches!(g.ty, Ty::Atom(_)) { 0 } else { 1 };
                (atom_prio, usize::MAX - ty_size(&g.ty), g.id as usize)
            });
            Some(goals[0].id)
        }
    }
}

fn expand_once(
    base: &SearchState,
    choices: &mut impl ChoiceStream,
    cfg: &SearchConfig,
    policy: &SearchPolicy,
    runtime: &mut SearchRuntime,
    metrics: &mut SearchMetrics,
) -> Option<SearchState> {
    let mut next = base.clone();
    let goal_id = select_goal_id(&next, choices, policy.goal_strategy)?;
    let goal = next.goals.remove(&goal_id)?;

    let (replacement, _) = synth(
        &mut next,
        &goal.ctx,
        &goal.ty,
        choices,
        cfg.synth_budget,
        goal.allow_case,
        policy,
        runtime,
        metrics,
    );

    if replace_hole(&mut next.root, goal_id, replacement) {
        Some(next)
    } else {
        None
    }
}

fn state_fingerprint(state: &SearchState) -> u64 {
    fn hash_ptm(
        tm: &PTm,
        st: &SearchState,
        hole_map: &mut HashMap<u32, u32>,
        next_id: &mut u32,
        h: &mut std::collections::hash_map::DefaultHasher,
    ) {
        match tm {
            PTm::Hole { id, .. } => {
                0u8.hash(h);
                let cid = *hole_map.entry(*id).or_insert_with(|| {
                    let v = *next_id;
                    *next_id += 1;
                    v
                });
                cid.hash(h);
                if let Some(g) = st.goals.get(id) {
                    g.ctx.hash(h);
                    g.ty.hash(h);
                    g.allow_case.hash(h);
                }
            }
            PTm::Var(i) => {
                1u8.hash(h);
                i.hash(h);
            }
            PTm::Lam { arg_ty, body } => {
                2u8.hash(h);
                arg_ty.hash(h);
                hash_ptm(body, st, hole_map, next_id, h);
            }
            PTm::App(f, x) => {
                3u8.hash(h);
                hash_ptm(f, st, hole_map, next_id, h);
                hash_ptm(x, st, hole_map, next_id, h);
            }
            PTm::Pair(a, b) => {
                4u8.hash(h);
                hash_ptm(a, st, hole_map, next_id, h);
                hash_ptm(b, st, hole_map, next_id, h);
            }
            PTm::Inl { rhs_ty, term } => {
                5u8.hash(h);
                rhs_ty.hash(h);
                hash_ptm(term, st, hole_map, next_id, h);
            }
            PTm::Inr { lhs_ty, term } => {
                6u8.hash(h);
                lhs_ty.hash(h);
                hash_ptm(term, st, hole_map, next_id, h);
            }
            PTm::Case { scrut, left, right } => {
                7u8.hash(h);
                hash_ptm(scrut, st, hole_map, next_id, h);
                hash_ptm(left, st, hole_map, next_id, h);
                hash_ptm(right, st, hole_map, next_id, h);
            }
            PTm::Fst(t) => {
                8u8.hash(h);
                hash_ptm(t, st, hole_map, next_id, h);
            }
            PTm::Snd(t) => {
                9u8.hash(h);
                hash_ptm(t, st, hole_map, next_id, h);
            }
            PTm::Absurd {
                bot_term,
                target_ty,
            } => {
                10u8.hash(h);
                target_ty.hash(h);
                hash_ptm(bot_term, st, hole_map, next_id, h);
            }
        }
    }

    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    let mut hole_map = HashMap::new();
    let mut next_id = 0u32;
    hash_ptm(&state.root, state, &mut hole_map, &mut next_id, &mut hasher);

    // root に現れない余剰 goal も fingerprint に反映して整合性バグを炙る
    let mut leftovers: Vec<(u32, Ty, bool)> = state
        .goals
        .iter()
        .filter_map(|(id, g)| {
            if hole_map.contains_key(id) {
                None
            } else {
                Some((ctx_fingerprint(&g.ctx) as u32, g.ty.clone(), g.allow_case))
            }
        })
        .collect();
    leftovers.sort_by_key(|(c, t, ac)| (*c, ty_size(t), *ac));
    leftovers.hash(&mut hasher);

    hasher.finish()
}

pub fn beam_search(
    ctx: &Ctx,
    target: &Ty,
    choices: &mut impl ChoiceStream,
    cfg: &SearchConfig,
    policy: &SearchPolicy,
) -> SearchOutcome {
    let mut beam = vec![SearchState::new(ctx, target)];
    let mut metrics = SearchMetrics::default();
    let mut runtime = SearchRuntime::default();
    metrics.observe_state(&beam[0]);

    for iter in 0..cfg.max_iters {
        metrics.iterations = iter + 1;

        let mut best_complete: Option<(Tm, i64, SearchState)> = None;
        for state in &beam {
            if let Some(tm) = try_finalize(state) {
                let sc = score_partial(state);
                match &best_complete {
                    Some((_, best_sc, _)) if *best_sc >= sc => {}
                    _ => best_complete = Some((tm, sc, state.clone())),
                }
            }
        }
        if let Some((tm, sc, state)) = best_complete {
            metrics.observe_state(&state);
            return SearchOutcome {
                best_state: state,
                best_score: sc,
                complete_term: Some(tm),
                metrics,
            };
        }

        let mut candidates = Vec::new();
        for state in &beam {
            candidates.push(state.clone());
            for _ in 0..cfg.expand_per_state.max(1) {
                if let Some(next) =
                    expand_once(state, choices, cfg, policy, &mut runtime, &mut metrics)
                {
                    metrics.expanded_states += 1;
                    metrics.observe_state(&next);
                    candidates.push(next);
                    let (repair_rounds, repair_cap) = if cfg.synth_budget <= 3 || cfg.max_iters <= 8
                    {
                        (3, 48)
                    } else {
                        (2, 40)
                    };
                    let repaired = greedy_local_repair(
                        candidates.last().expect("pushed"),
                        repair_rounds,
                        repair_cap,
                        &mut metrics,
                    );
                    if score_partial(&repaired) > score_partial(candidates.last().expect("pushed"))
                    {
                        metrics.observe_state(&repaired);
                        candidates.push(repaired);
                        metrics.repair_promoted_states += 1;
                    }
                }
            }
        }

        // 同一状態の焼き増しを除去しスコア最大のものだけ残す
        let before = candidates.len();
        let mut uniq: HashMap<u64, SearchState> = HashMap::new();
        for st in candidates {
            let fp = state_fingerprint(&st);
            match uniq.get(&fp) {
                Some(prev) if score_partial(prev) >= score_partial(&st) => {}
                _ => {
                    uniq.insert(fp, st);
                }
            }
        }
        let mut deduped: Vec<SearchState> = uniq.into_values().collect();
        metrics.dedup_dropped += before.saturating_sub(deduped.len());

        deduped.sort_by_key(|s| -score_partial(s));
        let bw = cfg.beam_width.max(1);
        if deduped.len() > bw {
            deduped.truncate(bw);
        }
        beam = deduped;
    }

    let mut best = beam[0].clone();
    let mut best_sc = score_partial(&best);
    for s in beam.iter().skip(1) {
        let sc = score_partial(s);
        if sc > best_sc {
            best = s.clone();
            best_sc = sc;
        }
    }
    metrics.observe_state(&best);
    let complete = try_finalize(&best);
    SearchOutcome {
        best_state: best,
        best_score: best_sc,
        complete_term: complete,
        metrics,
    }
}
