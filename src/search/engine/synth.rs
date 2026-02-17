use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use crate::kernel::ty_size;
use crate::kernel::{Ctx, Ty};

use super::super::{ChoiceStream, Goal, PTm, SearchMetrics, SearchPolicy, SearchState, ptm_size};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct SynthMemoKey {
    ctx_fp: u64,
    ty: Ty,
    budget_bucket: u32,
    allow_case: bool,
    policy_sig: u64,
}

#[derive(Clone, Debug)]
enum SynthMemo {
    Solved(PTm),
    Failed,
}

#[derive(Default)]
pub(super) struct SearchRuntime {
    memo: HashMap<SynthMemoKey, SynthMemo>,
    a_success_freq: HashMap<Ty, u32>,
}

impl SearchRuntime {
    fn hit_memo(&self, key: &SynthMemoKey) -> Option<SynthMemo> {
        self.memo.get(key).cloned()
    }

    fn note_a(&mut self, ty: &Ty) {
        *self.a_success_freq.entry(ty.clone()).or_insert(0) += 1;
    }

    fn freq(&self, ty: &Ty) -> u32 {
        self.a_success_freq.get(ty).copied().unwrap_or(0)
    }
}

pub(super) fn ctx_fingerprint(ctx: &Ctx) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    ctx.hash(&mut h);
    h.finish()
}

fn synth_budget_bucket(budget: u32) -> u32 {
    match budget {
        0..=2 => 2,
        3..=5 => 5,
        6..=9 => 9,
        10..=14 => 14,
        _ => 20,
    }
}

fn weighted_pick(options: &[(u32, u32)], choices: &mut impl ChoiceStream) -> u32 {
    let total = options.iter().map(|(_, w)| *w as u64).sum::<u64>();
    if total == 0 {
        return options[0].0;
    }
    let mut r = (choices.next_u32() as u64) % total;
    for (v, w) in options {
        if r < (*w as u64) {
            return *v;
        }
        r -= *w as u64;
    }
    options[0].0
}

fn collect_subtypes(ty: &Ty, set: &mut HashSet<Ty>) {
    if !set.insert(ty.clone()) {
        return;
    }
    match ty {
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            collect_subtypes(a, set);
            collect_subtypes(b, set);
        }
        Ty::Atom(_) | Ty::Bot => {}
    }
}

fn rank_intermediate_types(ctx: &Ctx, target: &Ty, runtime: &SearchRuntime) -> Vec<Ty> {
    let mut set = HashSet::new();
    collect_subtypes(target, &mut set);
    for ty in ctx {
        collect_subtypes(ty, &mut set);
    }

    let target_subs = {
        let mut s = HashSet::new();
        collect_subtypes(target, &mut s);
        s
    };

    let base: Vec<Ty> = set.iter().cloned().collect();
    for a in base.iter().take(6) {
        set.insert(Ty::Prod(Box::new(target.clone()), Box::new(a.clone())));
        set.insert(Ty::Prod(Box::new(a.clone()), Box::new(target.clone())));
    }

    let mut v: Vec<Ty> = set.into_iter().collect();
    v.sort_by_key(|a| {
        let mut s = (ty_size(a) as i64) * 8;
        if target_subs.contains(a) {
            s -= 16;
        }
        if ctx
            .iter()
            .any(|t| t == &Ty::Arr(Box::new(a.clone()), Box::new(target.clone())))
        {
            s -= 30;
        }
        s -= (runtime.freq(a) as i64) * 3;
        s
    });
    v
}

fn ptm_has_hole(tm: &PTm) -> bool {
    match tm {
        PTm::Hole { .. } => true,
        PTm::Var(_) => false,
        PTm::Lam { body, .. } => ptm_has_hole(body),
        PTm::App(f, x) | PTm::Pair(f, x) => ptm_has_hole(f) || ptm_has_hole(x),
        PTm::Inl { term, .. } | PTm::Inr { term, .. } => ptm_has_hole(term),
        PTm::Case { scrut, left, right } => {
            ptm_has_hole(scrut) || ptm_has_hole(left) || ptm_has_hole(right)
        }
        PTm::Fst(t) | PTm::Snd(t) => ptm_has_hole(t),
        PTm::Absurd { bot_term, .. } => ptm_has_hole(bot_term),
    }
}

fn ctx_db_entries(ctx: &Ctx) -> Vec<(u32, Ty)> {
    let mut out = Vec::new();
    for i in 0..ctx.len() {
        let db = i as u32;
        let ty = ctx[ctx.len() - 1 - i].clone();
        out.push((db, ty));
    }
    out
}

fn collect_projection_pool(ctx: &Ctx, max_depth: usize, cap: usize) -> Vec<(PTm, Ty, u32)> {
    let entries = ctx_db_entries(ctx);
    let mut pool: Vec<(PTm, Ty, u32)> = Vec::new();
    let mut seen: HashMap<PTm, usize> = HashMap::new();
    let mut frontier: Vec<usize> = Vec::new();

    for (db, ty) in entries {
        let tm = PTm::Var(db);
        let idx = pool.len();
        pool.push((tm.clone(), ty, 0));
        seen.insert(tm, idx);
        frontier.push(idx);
    }

    for _ in 0..max_depth {
        if frontier.is_empty() || pool.len() >= cap {
            break;
        }
        let mut next_frontier = Vec::new();
        for idx in frontier {
            let (base_tm, base_ty, base_cost) = match pool.get(idx) {
                Some((tm, ty, cost)) => (tm.clone(), ty.clone(), *cost),
                None => continue,
            };
            if let Ty::Prod(a, b) = base_ty {
                let c1 = PTm::Fst(Box::new(base_tm.clone()));
                if !seen.contains_key(&c1) && pool.len() < cap {
                    let id = pool.len();
                    pool.push((c1.clone(), *a, base_cost + 1));
                    seen.insert(c1, id);
                    next_frontier.push(id);
                }
                let c2 = PTm::Snd(Box::new(base_tm));
                if !seen.contains_key(&c2) && pool.len() < cap {
                    let id = pool.len();
                    pool.push((c2.clone(), *b, base_cost + 1));
                    seen.insert(c2, id);
                    next_frontier.push(id);
                }
            }
        }
        frontier = next_frontier;
    }

    pool
}

pub(crate) fn collect_case_scrutinees(ctx: &Ctx) -> Vec<PTm> {
    let entries = ctx_db_entries(ctx);
    let mut out = Vec::new();
    let mut seen = HashSet::<PTm>::new();
    let proj_pool = collect_projection_pool(ctx, 3, 96);

    // Stage 1: 射影閉包項で既に合計型を持つもの
    for (tm, ty, _) in &proj_pool {
        if matches!(ty, Ty::Sum(_, _)) && seen.insert(tm.clone()) {
            out.push(tm.clone());
        }
    }

    // Stage 2: Var(f):X->(A+B) を、X の射影閉包引数項に適用したもの
    let mut args_by_ty: HashMap<Ty, Vec<PTm>> = HashMap::new();
    for (tm, ty, _) in &proj_pool {
        args_by_ty.entry(ty.clone()).or_default().push(tm.clone());
    }
    for (fdb, fty) in &entries {
        if let Ty::Arr(x, y) = fty {
            if !matches!(y.as_ref(), Ty::Sum(_, _)) {
                continue;
            }
            if let Some(arg_terms) = args_by_ty.get(x.as_ref()) {
                for arg_tm in arg_terms.iter().take(12) {
                    let tm = PTm::App(Box::new(PTm::Var(*fdb)), Box::new(arg_tm.clone()));
                    if seen.insert(tm.clone()) {
                        out.push(tm);
                    }
                }
            }
        }
    }

    out
}

fn collect_direct_app_candidates(ctx: &Ctx, target: &Ty) -> Vec<(PTm, Ty, u32)> {
    let mut out = Vec::new();
    let mut seen = HashSet::<PTm>::new();
    // 射影閉包から関数候補を取ることで fst/snd 由来の関数も直接適用できるように
    let pool = collect_projection_pool(ctx, 4, 128);
    for (tm, ty, cost) in pool {
        if let Ty::Arr(a, b) = ty
            && *b == *target
            && seen.insert(tm.clone())
        {
            out.push((tm, *a, cost));
        }
    }
    out.sort_by_key(|(f, a, cost)| (*cost, ty_size(a), ptm_size(f)));
    out
}

fn collect_shallow_material_terms(ctx: &Ctx, target: &Ty) -> Vec<PTm> {
    let depth = ty_size(target).min(4);
    let mut out = collect_projection_pool(ctx, depth, 128)
        .into_iter()
        .filter_map(|(tm, ty, cost)| {
            if &ty == target {
                Some((cost, tm))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    out.sort_by_key(|(cost, tm)| (*cost, ptm_size(tm)));
    let out: Vec<PTm> = out.into_iter().map(|(_, tm)| tm).take(24).collect();
    out
}

fn collect_material_terms(ctx: &Ctx, target: &Ty) -> Vec<PTm> {
    let entries = ctx_db_entries(ctx);
    let mut scored: Vec<(u32, PTm)> = Vec::new();
    let mut seen = HashSet::new();

    for tm in collect_shallow_material_terms(ctx, target) {
        if seen.insert(tm.clone()) {
            let score = match tm {
                PTm::Var(_) => 0,
                PTm::Fst(_) | PTm::Snd(_) => 1,
                _ => 3,
            };
            scored.push((score, tm));
        }
    }

    let pool = collect_projection_pool(ctx, 4, 128);
    let mut args_by_ty: HashMap<Ty, Vec<(u32, PTm)>> = HashMap::new();
    for (tm, ty, cost) in pool {
        args_by_ty.entry(ty).or_default().push((cost, tm));
    }
    for v in args_by_ty.values_mut() {
        v.sort_by_key(|(cost, tm)| (*cost, ptm_size(tm)));
        if v.len() > 20 {
            v.truncate(20);
        }
    }

    for (fdb, fty) in &entries {
        let (arg_ty, ret_ty) = match fty {
            Ty::Arr(a, b) => (a.as_ref(), b.as_ref()),
            _ => continue,
        };
        if ret_ty != target {
            continue;
        }
        if let Some(args) = args_by_ty.get(arg_ty) {
            for (_, arg) in args {
                let tm = PTm::App(Box::new(PTm::Var(*fdb)), Box::new(arg.clone()));
                if seen.insert(tm.clone()) {
                    scored.push((2, tm));
                }
            }
        }
    }

    if let Ty::Prod(a, b) = target {
        let lhs = collect_shallow_material_terms(ctx, a);
        let rhs = collect_shallow_material_terms(ctx, b);
        for l in lhs.iter().take(8) {
            for r in rhs.iter().take(8) {
                let tm = PTm::Pair(Box::new(l.clone()), Box::new(r.clone()));
                if seen.insert(tm.clone()) {
                    scored.push((2, tm));
                }
            }
        }
    }

    if let Ty::Sum(a, b) = target {
        for l in collect_shallow_material_terms(ctx, a).into_iter().take(10) {
            let tm = PTm::Inl {
                rhs_ty: (**b).clone(),
                term: Box::new(l),
            };
            if seen.insert(tm.clone()) {
                scored.push((2, tm));
            }
        }
        for r in collect_shallow_material_terms(ctx, b).into_iter().take(10) {
            let tm = PTm::Inr {
                lhs_ty: (**a).clone(),
                term: Box::new(r),
            };
            if seen.insert(tm.clone()) {
                scored.push((2, tm));
            }
        }
    }

    if target != &Ty::Bot {
        for (db, ty) in &entries {
            if matches!(ty, Ty::Bot) {
                let tm = PTm::Absurd {
                    bot_term: Box::new(PTm::Var(*db)),
                    target_ty: target.clone(),
                };
                if seen.insert(tm.clone()) {
                    scored.push((3, tm));
                }
            }
        }
    }

    scored.sort_by_key(|(s, tm)| (*s, ptm_size(tm)));
    scored.into_iter().map(|(_, tm)| tm).collect()
}

#[allow(clippy::too_many_arguments)]
fn synth_material_first(
    state: &mut SearchState,
    ctx: &Ctx,
    target: &Ty,
    choices: &mut impl ChoiceStream,
    budget: u32,
    allow_case: bool,
    policy: &SearchPolicy,
    runtime: &mut SearchRuntime,
    metrics: &mut SearchMetrics,
) -> (PTm, bool) {
    let mats = collect_material_terms(ctx, target);
    if !mats.is_empty() {
        let pick = weighted_pick(
            &[
                (
                    0,
                    policy
                        .w_var
                        .saturating_add(policy.w_proj)
                        .saturating_add(policy.w_direct_app)
                        .max(1),
                ),
                (1, policy.w_hole.saturating_add(2).max(1)),
            ],
            choices,
        );
        if pick == 0 || budget <= 1 {
            let idx = (choices.next_u32() as usize) % mats.len();
            return (mats[idx].clone(), false);
        }
    }
    synth(
        state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
    )
}

fn branch_policy(base: &SearchPolicy, introduced: &Ty, target: &Ty) -> SearchPolicy {
    let mut p = base.clone();
    p.w_hole = p.w_hole.saturating_add(2);
    p.w_case = p.w_case.saturating_sub(1).max(1);
    p.w_absurd = p.w_absurd.saturating_sub(1).max(1);
    match target {
        Ty::Prod(_, _) => {
            p.w_pair = p.w_pair.saturating_add(10);
            p.w_var = p.w_var.saturating_add(3);
        }
        Ty::Sum(_, _) => {
            p.w_sum_intro = p.w_sum_intro.saturating_add(10);
            p.w_case = p.w_case.saturating_sub(1).max(1);
            p.w_var = p.w_var.saturating_add(2);
        }
        Ty::Atom(_) | Ty::Bot => {
            p.w_var = p.w_var.saturating_add(10);
            p.w_direct_app = p.w_direct_app.saturating_add(6);
            p.w_app = p.w_app.saturating_sub(1).max(1);
        }
        Ty::Arr(_, _) => {
            p.w_var = p.w_var.saturating_add(6);
        }
    }
    // 分岐で導入された変数が和型なら追加の case 分解が有効になりやすい
    if matches!(introduced, Ty::Sum(_, _)) {
        p.w_case = p.w_case.saturating_add(4);
        p.w_sum_intro = p.w_sum_intro.saturating_add(1);
    }
    if introduced == target {
        p.w_var = p.w_var.saturating_add(8);
    }
    p
}

fn shift_ptm_indices(d: i32, cutoff: u32, tm: &PTm) -> PTm {
    match tm {
        PTm::Hole { id, ty } => PTm::Hole {
            id: *id,
            ty: ty.clone(),
        },
        PTm::Var(k) => {
            if *k >= cutoff {
                let nk = ((*k as i64) + (d as i64)).max(0) as u32;
                PTm::Var(nk)
            } else {
                PTm::Var(*k)
            }
        }
        PTm::Lam { arg_ty, body } => PTm::Lam {
            arg_ty: arg_ty.clone(),
            body: Box::new(shift_ptm_indices(d, cutoff + 1, body)),
        },
        PTm::App(f, x) => PTm::App(
            Box::new(shift_ptm_indices(d, cutoff, f)),
            Box::new(shift_ptm_indices(d, cutoff, x)),
        ),
        PTm::Pair(a, b) => PTm::Pair(
            Box::new(shift_ptm_indices(d, cutoff, a)),
            Box::new(shift_ptm_indices(d, cutoff, b)),
        ),
        PTm::Inl { rhs_ty, term } => PTm::Inl {
            rhs_ty: rhs_ty.clone(),
            term: Box::new(shift_ptm_indices(d, cutoff, term)),
        },
        PTm::Inr { lhs_ty, term } => PTm::Inr {
            lhs_ty: lhs_ty.clone(),
            term: Box::new(shift_ptm_indices(d, cutoff, term)),
        },
        PTm::Case { scrut, left, right } => PTm::Case {
            scrut: Box::new(shift_ptm_indices(d, cutoff, scrut)),
            left: Box::new(shift_ptm_indices(d, cutoff + 1, left)),
            right: Box::new(shift_ptm_indices(d, cutoff + 1, right)),
        },
        PTm::Fst(t) => PTm::Fst(Box::new(shift_ptm_indices(d, cutoff, t))),
        PTm::Snd(t) => PTm::Snd(Box::new(shift_ptm_indices(d, cutoff, t))),
        PTm::Absurd {
            bot_term,
            target_ty,
        } => PTm::Absurd {
            bot_term: Box::new(shift_ptm_indices(d, cutoff, bot_term)),
            target_ty: target_ty.clone(),
        },
    }
}

fn subst_ptm_indices(j: u32, s: &PTm, tm: &PTm) -> PTm {
    fn walk(c: u32, j: u32, s: &PTm, tm: &PTm) -> PTm {
        match tm {
            PTm::Hole { id, ty } => PTm::Hole {
                id: *id,
                ty: ty.clone(),
            },
            PTm::Var(k) => {
                if *k == j + c {
                    shift_ptm_indices(c as i32, 0, s)
                } else {
                    PTm::Var(*k)
                }
            }
            PTm::Lam { arg_ty, body } => PTm::Lam {
                arg_ty: arg_ty.clone(),
                body: Box::new(walk(c + 1, j, s, body)),
            },
            PTm::App(f, x) => PTm::App(Box::new(walk(c, j, s, f)), Box::new(walk(c, j, s, x))),
            PTm::Pair(a, b) => PTm::Pair(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b))),
            PTm::Inl { rhs_ty, term } => PTm::Inl {
                rhs_ty: rhs_ty.clone(),
                term: Box::new(walk(c, j, s, term)),
            },
            PTm::Inr { lhs_ty, term } => PTm::Inr {
                lhs_ty: lhs_ty.clone(),
                term: Box::new(walk(c, j, s, term)),
            },
            PTm::Case { scrut, left, right } => PTm::Case {
                scrut: Box::new(walk(c, j, s, scrut)),
                left: Box::new(walk(c + 1, j, s, left)),
                right: Box::new(walk(c + 1, j, s, right)),
            },
            PTm::Fst(t) => PTm::Fst(Box::new(walk(c, j, s, t))),
            PTm::Snd(t) => PTm::Snd(Box::new(walk(c, j, s, t))),
            PTm::Absurd {
                bot_term,
                target_ty,
            } => PTm::Absurd {
                bot_term: Box::new(walk(c, j, s, bot_term)),
                target_ty: target_ty.clone(),
            },
        }
    }
    walk(0, j, s, tm)
}

fn subst_top_ptm_indices(s: &PTm, body: &PTm) -> PTm {
    let su = shift_ptm_indices(1, 0, s);
    let sub = subst_ptm_indices(0, &su, body);
    shift_ptm_indices(-1, 0, &sub)
}

fn cheap_step_ptm(tm: &PTm) -> Option<PTm> {
    match tm {
        PTm::Fst(t) => match t.as_ref() {
            PTm::Pair(a, _) => Some((**a).clone()),
            _ => cheap_step_ptm(t).map(|n| PTm::Fst(Box::new(n))),
        },
        PTm::Snd(t) => match t.as_ref() {
            PTm::Pair(_, b) => Some((**b).clone()),
            _ => cheap_step_ptm(t).map(|n| PTm::Snd(Box::new(n))),
        },
        PTm::Case { scrut, left, right } => match scrut.as_ref() {
            PTm::Inl { term, .. } => Some(subst_top_ptm_indices(term, left)),
            PTm::Inr { term, .. } => Some(subst_top_ptm_indices(term, right)),
            _ => cheap_step_ptm(scrut).map(|n| PTm::Case {
                scrut: Box::new(n),
                left: left.clone(),
                right: right.clone(),
            }),
        },
        PTm::Lam { arg_ty, body } => cheap_step_ptm(body).map(|n| PTm::Lam {
            arg_ty: arg_ty.clone(),
            body: Box::new(n),
        }),
        PTm::App(f, x) => {
            if let Some(nf) = cheap_step_ptm(f) {
                Some(PTm::App(Box::new(nf), x.clone()))
            } else {
                cheap_step_ptm(x).map(|nx| PTm::App(f.clone(), Box::new(nx)))
            }
        }
        PTm::Pair(a, b) => {
            if let Some(na) = cheap_step_ptm(a) {
                Some(PTm::Pair(Box::new(na), b.clone()))
            } else {
                cheap_step_ptm(b).map(|nb| PTm::Pair(a.clone(), Box::new(nb)))
            }
        }
        PTm::Inl { rhs_ty, term } => cheap_step_ptm(term).map(|n| PTm::Inl {
            rhs_ty: rhs_ty.clone(),
            term: Box::new(n),
        }),
        PTm::Inr { lhs_ty, term } => cheap_step_ptm(term).map(|n| PTm::Inr {
            lhs_ty: lhs_ty.clone(),
            term: Box::new(n),
        }),
        PTm::Absurd {
            bot_term,
            target_ty,
        } => cheap_step_ptm(bot_term).map(|n| PTm::Absurd {
            bot_term: Box::new(n),
            target_ty: target_ty.clone(),
        }),
        PTm::Hole { .. } | PTm::Var(_) => None,
    }
}

pub(super) fn cheap_normalize_ptm(tm: &PTm, max_steps: usize) -> PTm {
    let mut cur = tm.clone();
    for _ in 0..max_steps {
        if let Some(n) = cheap_step_ptm(&cur) {
            cur = n;
        } else {
            break;
        }
    }
    cur
}

pub(crate) fn scrutinee_fingerprint(scrut: &PTm, binder_depth: u32) -> u64 {
    let lifted = shift_ptm_indices(binder_depth as i32, 0, scrut);
    let normalized = cheap_normalize_ptm(&lifted, 16);
    let mut h = std::collections::hash_map::DefaultHasher::new();
    normalized.hash(&mut h);
    h.finish()
}

fn contains_case_on_scrutinee(tm: &PTm, scrut: &PTm) -> bool {
    fn go(tm: &PTm, scrut: &PTm, binders: u32) -> bool {
        match tm {
            PTm::Case {
                scrut: s,
                left,
                right,
            } => {
                let outer_fp = scrutinee_fingerprint(scrut, binders);
                let inner_fp = scrutinee_fingerprint(s, 0);
                if inner_fp == outer_fp {
                    return true;
                }
                go(s, scrut, binders)
                    || go(left, scrut, binders + 1)
                    || go(right, scrut, binders + 1)
            }
            PTm::Lam { body, .. } => go(body, scrut, binders + 1),
            PTm::App(f, x) | PTm::Pair(f, x) => go(f, scrut, binders) || go(x, scrut, binders),
            PTm::Inl { term, .. } | PTm::Inr { term, .. } => go(term, scrut, binders),
            PTm::Fst(t) | PTm::Snd(t) => go(t, scrut, binders),
            PTm::Absurd { bot_term, .. } => go(bot_term, scrut, binders),
            PTm::Hole { .. } | PTm::Var(_) => false,
        }
    }
    go(tm, scrut, 0)
}

fn try_infer_ptm_type(ctx: &Ctx, tm: &PTm) -> Option<Ty> {
    match tm {
        PTm::Hole { .. } => None,
        PTm::Var(i) => {
            let idx = *i as usize;
            if idx >= ctx.len() {
                return None;
            }
            Some(ctx[ctx.len() - 1 - idx].clone())
        }
        PTm::Lam { arg_ty, body } => {
            let mut ext = ctx.clone();
            ext.push(arg_ty.clone());
            let body_ty = try_infer_ptm_type(&ext, body)?;
            Some(Ty::Arr(Box::new(arg_ty.clone()), Box::new(body_ty)))
        }
        PTm::App(f, x) => {
            let f_ty = try_infer_ptm_type(ctx, f)?;
            let x_ty = try_infer_ptm_type(ctx, x)?;
            match f_ty {
                Ty::Arr(a, b) if *a == x_ty => Some(*b),
                _ => None,
            }
        }
        PTm::Pair(a, b) => {
            let a_ty = try_infer_ptm_type(ctx, a)?;
            let b_ty = try_infer_ptm_type(ctx, b)?;
            Some(Ty::Prod(Box::new(a_ty), Box::new(b_ty)))
        }
        PTm::Inl { rhs_ty, term } => {
            let lhs_ty = try_infer_ptm_type(ctx, term)?;
            Some(Ty::Sum(Box::new(lhs_ty), Box::new(rhs_ty.clone())))
        }
        PTm::Inr { lhs_ty, term } => {
            let rhs_ty = try_infer_ptm_type(ctx, term)?;
            Some(Ty::Sum(Box::new(lhs_ty.clone()), Box::new(rhs_ty)))
        }
        PTm::Case { scrut, left, right } => {
            let st = try_infer_ptm_type(ctx, scrut)?;
            match st {
                Ty::Sum(a, b) => {
                    let mut lctx = ctx.clone();
                    lctx.push((*a).clone());
                    let mut rctx = ctx.clone();
                    rctx.push((*b).clone());
                    let lt = try_infer_ptm_type(&lctx, left)?;
                    let rt = try_infer_ptm_type(&rctx, right)?;
                    if lt == rt { Some(lt) } else { None }
                }
                _ => None,
            }
        }
        PTm::Fst(t) => match try_infer_ptm_type(ctx, t)? {
            Ty::Prod(a, _) => Some(*a),
            _ => None,
        },
        PTm::Snd(t) => match try_infer_ptm_type(ctx, t)? {
            Ty::Prod(_, b) => Some(*b),
            _ => None,
        },
        PTm::Absurd {
            bot_term,
            target_ty,
        } => match try_infer_ptm_type(ctx, bot_term)? {
            Ty::Bot => Some(target_ty.clone()),
            _ => None,
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn synth(
    state: &mut SearchState,
    ctx: &Ctx,
    target: &Ty,
    choices: &mut impl ChoiceStream,
    budget: u32,
    allow_case: bool,
    policy: &SearchPolicy,
    runtime: &mut SearchRuntime,
    metrics: &mut SearchMetrics,
) -> (PTm, bool) {
    let key = SynthMemoKey {
        ctx_fp: ctx_fingerprint(ctx),
        ty: target.clone(),
        budget_bucket: synth_budget_bucket(budget),
        allow_case,
        policy_sig: policy.signature(),
    };

    if let Some(m) = runtime.hit_memo(&key) {
        metrics.memo_hits += 1;
        return match m {
            SynthMemo::Solved(tm) => (tm, false),
            SynthMemo::Failed => (
                state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                true,
            ),
        };
    }

    let (tm, forced_fail) = synth_uncached(
        state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
    );

    if !ptm_has_hole(&tm) {
        runtime.memo.insert(key, SynthMemo::Solved(tm.clone()));
    } else if forced_fail {
        runtime.memo.insert(key, SynthMemo::Failed);
    }

    (tm, forced_fail)
}

#[allow(clippy::too_many_arguments)]
fn synth_uncached(
    state: &mut SearchState,
    ctx: &Ctx,
    target: &Ty,
    choices: &mut impl ChoiceStream,
    budget: u32,
    allow_case: bool,
    policy: &SearchPolicy,
    runtime: &mut SearchRuntime,
    metrics: &mut SearchMetrics,
) -> (PTm, bool) {
    if budget == 0 {
        return (
            state.fresh_hole(ctx.clone(), target.clone(), allow_case),
            true,
        );
    }

    match target {
        Ty::Arr(a, b) => {
            let branch = weighted_pick(
                &[
                    (0, 10),
                    (1, policy.w_var.max(1)),
                    (2, policy.w_app.max(1)),
                    (3, policy.w_hole.max(1)),
                ],
                choices,
            );
            if branch == 0 {
                let mut ext = ctx.clone();
                ext.push((**a).clone());
                let (body, ff) = synth(
                    state,
                    &ext,
                    b,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                return (
                    PTm::Lam {
                        arg_ty: (**a).clone(),
                        body: Box::new(body),
                    },
                    ff,
                );
            }
            synth_non_arrow(
                state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
            )
        }
        Ty::Prod(a, b) => {
            let branch = weighted_pick(
                &[(0, policy.w_pair.max(1)), (1, policy.w_hole.max(1))],
                choices,
            );
            if branch == 0 {
                let (l, ff1) = synth_material_first(
                    state,
                    ctx,
                    a,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                let (r, ff2) = synth_material_first(
                    state,
                    ctx,
                    b,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                return (PTm::Pair(Box::new(l), Box::new(r)), ff1 && ff2);
            }
            (
                state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                false,
            )
        }
        Ty::Sum(a, b) => {
            let case_scruts = collect_case_scrutinees(ctx);
            let can_sum_non_intro = budget > 1 && !case_scruts.is_empty();
            let branch = weighted_pick(
                &[
                    (0, policy.w_sum_intro.max(1)),
                    (1, policy.w_sum_intro.max(1)),
                    (
                        3,
                        if can_sum_non_intro {
                            policy.w_case.max(1)
                        } else {
                            0
                        },
                    ),
                    (2, policy.w_hole.max(1)),
                ],
                choices,
            );
            match branch {
                0 => {
                    let (t, ff) = synth_material_first(
                        state,
                        ctx,
                        a,
                        choices,
                        budget - 1,
                        allow_case,
                        policy,
                        runtime,
                        metrics,
                    );
                    (
                        PTm::Inl {
                            rhs_ty: (**b).clone(),
                            term: Box::new(t),
                        },
                        ff,
                    )
                }
                1 => {
                    let (t, ff) = synth_material_first(
                        state,
                        ctx,
                        b,
                        choices,
                        budget - 1,
                        allow_case,
                        policy,
                        runtime,
                        metrics,
                    );
                    (
                        PTm::Inr {
                            lhs_ty: (**a).clone(),
                            term: Box::new(t),
                        },
                        ff,
                    )
                }
                3 => synth_non_arrow(
                    state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
                ),
                _ => (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                ),
            }
        }
        Ty::Atom(_) | Ty::Bot => synth_non_arrow(
            state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn synth_non_arrow(
    state: &mut SearchState,
    ctx: &Ctx,
    target: &Ty,
    choices: &mut impl ChoiceStream,
    budget: u32,
    allow_case: bool,
    policy: &SearchPolicy,
    runtime: &mut SearchRuntime,
    metrics: &mut SearchMetrics,
) -> (PTm, bool) {
    if matches!(target, Ty::Atom(_)) && !ctx.is_empty() && ctx[ctx.len() - 1] == *target {
        return (PTm::Var(0), false);
    }

    let mut vars: Vec<u32> = Vec::new();
    for i in 0..ctx.len() {
        let db = i as u32;
        let ty = &ctx[ctx.len() - 1 - i];
        if ty == target {
            vars.push(db);
        }
    }

    let aset = rank_intermediate_types(ctx, target, runtime);
    let direct_apps = collect_direct_app_candidates(ctx, target);
    let can_direct_app = budget > 1 && !direct_apps.is_empty();
    let can_app = budget > 1 && !aset.is_empty();
    let can_proj = budget > 1 && !aset.is_empty();
    let case_scruts = collect_case_scrutinees(ctx);
    // allow_case は Case の重み調整に残しつつ、完全禁止には使わない
    // 同一 scrutinee の再 Case は contains_case_on_scrutinee で抑制する
    let can_case = budget > 1 && !case_scruts.is_empty();

    let mut options: Vec<(u32, u32)> = Vec::new();
    if !vars.is_empty() {
        options.push((0, policy.w_var.max(1)));
    }
    if can_app {
        options.push((1, policy.w_app.max(1)));
    }
    if can_direct_app {
        options.push((6, policy.w_direct_app.max(1)));
    }
    if can_proj {
        options.push((2, policy.w_proj.max(1)));
    }
    if budget > 1 && target != &Ty::Bot {
        options.push((4, policy.w_absurd.max(1)));
    }
    if can_case {
        options.push((5, policy.w_case.max(1)));
    }
    options.push((3, policy.w_hole.max(1)));

    let only_hole = options.len() == 1 && options[0].0 == 3;
    let pick = weighted_pick(&options, choices);
    match pick {
        0 => {
            let idx = (choices.next_u32() as usize) % vars.len();
            (PTm::Var(vars[idx]), false)
        }
        1 => {
            let a = aset[(choices.next_u32() as usize) % aset.len()].clone();
            runtime.note_a(&a);
            let f_ty = Ty::Arr(Box::new(a.clone()), Box::new(target.clone()));
            let (f, ff1) = synth(
                state,
                ctx,
                &f_ty,
                choices,
                budget - 1,
                allow_case,
                policy,
                runtime,
                metrics,
            );
            let (x, ff2) = synth(
                state,
                ctx,
                &a,
                choices,
                budget - 1,
                allow_case,
                policy,
                runtime,
                metrics,
            );
            (PTm::App(Box::new(f), Box::new(x)), ff1 && ff2)
        }
        6 => {
            let pick = (choices.next_u32() as usize) % direct_apps.len();
            let (f_tm, arg_ty, _) = direct_apps[pick].clone();
            runtime.note_a(&arg_ty);
            let (arg, ff) = synth(
                state,
                ctx,
                &arg_ty,
                choices,
                budget - 1,
                allow_case,
                policy,
                runtime,
                metrics,
            );
            (PTm::App(Box::new(f_tm), Box::new(arg)), ff)
        }
        2 => {
            let a = aset[(choices.next_u32() as usize) % aset.len()].clone();
            runtime.note_a(&a);
            let lr = choices.next_u32() % 2;
            if lr == 0 {
                let p_ty = Ty::Prod(Box::new(target.clone()), Box::new(a));
                let (p, ff) = synth(
                    state,
                    ctx,
                    &p_ty,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                (PTm::Fst(Box::new(p)), ff)
            } else {
                let p_ty = Ty::Prod(Box::new(a), Box::new(target.clone()));
                let (p, ff) = synth(
                    state,
                    ctx,
                    &p_ty,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                (PTm::Snd(Box::new(p)), ff)
            }
        }
        4 => {
            let (btm, ff) = synth(
                state,
                ctx,
                &Ty::Bot,
                choices,
                budget - 1,
                allow_case,
                policy,
                runtime,
                metrics,
            );
            (
                PTm::Absurd {
                    bot_term: Box::new(btm),
                    target_ty: target.clone(),
                },
                ff,
            )
        }
        5 => {
            if case_scruts.is_empty() {
                return (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                );
            }
            let pick = (choices.next_u32() as usize) % case_scruts.len();
            let scrut = case_scruts[pick].clone();
            let scrut_ty = match try_infer_ptm_type(ctx, &scrut) {
                Some(t) => t,
                None => {
                    return (
                        state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                        false,
                    );
                }
            };
            let (a, b) = match scrut_ty {
                Ty::Sum(a, b) => (*a, *b),
                _ => {
                    return (
                        state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                        false,
                    );
                }
            };

            let scale = policy.branch_budget_scale_per_mille.clamp(200, 1000);
            let branch_budget = (((budget - 1) as u64 * scale as u64) / 1000).max(1) as u32;
            let mut lctx = ctx.clone();
            lctx.push(a.clone());
            let mut rctx = ctx.clone();
            rctx.push(b.clone());
            let lp = branch_policy(policy, &a, target);
            let rp = branch_policy(policy, &b, target);
            let branch_allow_case = true;
            let (left, ff1) = synth(
                state,
                &lctx,
                target,
                choices,
                branch_budget,
                branch_allow_case,
                &lp,
                runtime,
                metrics,
            );
            let (right, ff2) = synth(
                state,
                &rctx,
                target,
                choices,
                branch_budget,
                branch_allow_case,
                &rp,
                runtime,
                metrics,
            );
            if contains_case_on_scrutinee(&left, &scrut)
                || contains_case_on_scrutinee(&right, &scrut)
            {
                return (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                );
            }
            (
                PTm::Case {
                    scrut: Box::new(scrut),
                    left: Box::new(left),
                    right: Box::new(right),
                },
                ff1 && ff2,
            )
        }
        _ => (
            state.fresh_hole(ctx.clone(), target.clone(), allow_case),
            only_hole,
        ),
    }
}

pub(super) fn replace_hole(node: &mut PTm, hole_id: u32, replacement: PTm) -> bool {
    let mut payload = Some(replacement);
    fn go(node: &mut PTm, hole_id: u32, payload: &mut Option<PTm>) -> bool {
        match node {
            PTm::Hole { id, .. } if *id == hole_id => {
                if let Some(tm) = payload.take() {
                    *node = tm;
                    return true;
                }
                false
            }
            PTm::Lam { body, .. } => go(body, hole_id, payload),
            PTm::App(f, x) | PTm::Pair(f, x) => go(f, hole_id, payload) || go(x, hole_id, payload),
            PTm::Inl { term, .. } | PTm::Inr { term, .. } => go(term, hole_id, payload),
            PTm::Case { scrut, left, right } => {
                go(scrut, hole_id, payload)
                    || go(left, hole_id, payload)
                    || go(right, hole_id, payload)
            }
            PTm::Fst(t) | PTm::Snd(t) => go(t, hole_id, payload),
            PTm::Absurd { bot_term, .. } => go(bot_term, hole_id, payload),
            _ => false,
        }
    }
    go(node, hole_id, &mut payload)
}

fn enum_small_closed_terms(ctx: &Ctx, target: &Ty, depth: usize, cap: usize) -> Vec<PTm> {
    if cap == 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut seen = HashSet::<PTm>::new();
    let push = |tm: PTm, out: &mut Vec<PTm>, seen: &mut HashSet<PTm>| {
        if !ptm_has_hole(&tm) && seen.insert(tm.clone()) {
            out.push(tm);
        }
    };

    for tm in collect_material_terms(ctx, target).into_iter().take(cap) {
        push(tm, &mut out, &mut seen);
        if out.len() >= cap {
            return out;
        }
    }

    if depth == 0 {
        return out;
    }

    match target {
        Ty::Arr(a, b) => {
            let mut ext = ctx.clone();
            ext.push((**a).clone());
            for body in enum_small_closed_terms(&ext, b, depth - 1, cap.min(16)) {
                push(
                    PTm::Lam {
                        arg_ty: (**a).clone(),
                        body: Box::new(body),
                    },
                    &mut out,
                    &mut seen,
                );
                if out.len() >= cap {
                    break;
                }
            }
        }
        Ty::Prod(a, b) => {
            let ls = enum_small_closed_terms(ctx, a, depth - 1, cap.min(12));
            let rs = enum_small_closed_terms(ctx, b, depth - 1, cap.min(12));
            for l in ls.iter().take(8) {
                for r in rs.iter().take(8) {
                    push(
                        PTm::Pair(Box::new(l.clone()), Box::new(r.clone())),
                        &mut out,
                        &mut seen,
                    );
                    if out.len() >= cap {
                        break;
                    }
                }
                if out.len() >= cap {
                    break;
                }
            }
        }
        Ty::Sum(a, b) => {
            for l in enum_small_closed_terms(ctx, a, depth - 1, cap.min(12))
                .into_iter()
                .take(10)
            {
                push(
                    PTm::Inl {
                        rhs_ty: (**b).clone(),
                        term: Box::new(l),
                    },
                    &mut out,
                    &mut seen,
                );
                if out.len() >= cap {
                    break;
                }
            }
            for r in enum_small_closed_terms(ctx, b, depth - 1, cap.min(12))
                .into_iter()
                .take(10)
            {
                push(
                    PTm::Inr {
                        lhs_ty: (**a).clone(),
                        term: Box::new(r),
                    },
                    &mut out,
                    &mut seen,
                );
                if out.len() >= cap {
                    break;
                }
            }
        }
        Ty::Atom(_) | Ty::Bot => {
            if depth > 0 {
                let scruts = collect_case_scrutinees(ctx);
                for scrut in scruts.into_iter().take(8) {
                    let Some(sty) = try_infer_ptm_type(ctx, &scrut) else {
                        continue;
                    };
                    let Ty::Sum(a, b) = sty else {
                        continue;
                    };
                    let mut lctx = ctx.clone();
                    lctx.push((*a).clone());
                    let mut rctx = ctx.clone();
                    rctx.push((*b).clone());

                    let lefts = enum_small_closed_terms(&lctx, target, depth - 1, cap.min(8));
                    let rights = enum_small_closed_terms(&rctx, target, depth - 1, cap.min(8));
                    let Some(left) = lefts.into_iter().next() else {
                        continue;
                    };
                    let Some(right) = rights.into_iter().next() else {
                        continue;
                    };
                    push(
                        PTm::Case {
                            scrut: Box::new(scrut),
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                        &mut out,
                        &mut seen,
                    );
                    if out.len() >= cap {
                        break;
                    }
                }
            }
        }
    }

    out
}

pub(super) fn greedy_local_repair(
    base: &SearchState,
    rounds: usize,
    candidate_cap: usize,
    metrics: &mut SearchMetrics,
) -> SearchState {
    let mut st = base.clone();
    metrics.repair_invocations += 1;
    for _ in 0..rounds {
        if st.goals.is_empty() {
            break;
        }
        let mut goals: Vec<Goal> = st.goals.values().cloned().collect();
        goals.sort_by_key(|g| (ty_size(&g.ty), g.ctx.len(), g.id));

        let mut changed = false;
        for g in goals {
            metrics.repair_goal_attempts += 1;
            let cands = enum_small_closed_terms(&g.ctx, &g.ty, 2, candidate_cap);
            if cands.is_empty() {
                continue;
            }

            let Some(tm) = cands.into_iter().next() else {
                continue;
            };
            metrics.repair_candidates_tried += 1;
            st.goals.remove(&g.id);
            if replace_hole(&mut st.root, g.id, tm) {
                metrics.repair_success_steps += 1;
                changed = true;
                break;
            }
            st.goals.insert(g.id, g);
        }

        if !changed {
            break;
        }
    }
    st
}
