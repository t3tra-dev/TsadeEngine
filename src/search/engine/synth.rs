use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use crate::kernel::ty_size;
use crate::kernel::{
    Ctx, FOTerm, Ty, fo_term_shift, fo_term_size, is_intuitionistic_theorem, ty_term_free_in,
    ty_term_shift, ty_term_subst_top,
};

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
        0 => 0,     // budget=0: always forced_fail (budget check), keep separate
        1 => 1,     // budget=1: no recursive options (can_subst=false), keep separate
        2..=5 => 5, // budget=2+: recursive options available (can_subst=true etc.)
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
        Ty::Forall(body) | Ty::Exists(body) => {
            collect_subtypes(body, set);
        }
        Ty::Atom(_) | Ty::Bot | Ty::Pred { .. } | Ty::Eq(_, _) => {}
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
        PTm::TLam { body } => ptm_has_hole(body),
        PTm::TApp { term, .. } => ptm_has_hole(term),
        PTm::Pack { body, .. } => ptm_has_hole(body),
        PTm::Unpack { scrut, body } => ptm_has_hole(scrut) || ptm_has_hole(body),
        PTm::Refl { .. } => false,
        PTm::Subst { eq_proof, body, .. } => ptm_has_hole(eq_proof) || ptm_has_hole(body),
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

fn collect_unpack_scrutinees(ctx: &Ctx) -> Vec<PTm> {
    let entries = ctx_db_entries(ctx);
    let mut out = Vec::new();
    let mut seen = HashSet::<PTm>::new();
    let proj_pool = collect_projection_pool(ctx, 3, 96);

    // Stage 1: projection-closure terms that already have ∃ type
    for (tm, ty, _) in &proj_pool {
        if matches!(ty, Ty::Exists(_)) && seen.insert(tm.clone()) {
            out.push(tm.clone());
        }
    }

    // Stage 2: apply functions of type X → ∃.φ to arguments of type X
    let mut args_by_ty: HashMap<Ty, Vec<PTm>> = HashMap::new();
    for (tm, ty, _) in &proj_pool {
        args_by_ty.entry(ty.clone()).or_default().push(tm.clone());
    }
    for (fdb, fty) in &entries {
        if let Ty::Arr(x, y) = fty {
            if !matches!(y.as_ref(), Ty::Exists(_)) {
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

fn collect_witness_pool(ctx: &Ctx, target: &Ty) -> Vec<FOTerm> {
    fn shift_fo_out(tm: &FOTerm, depth: u32) -> Option<FOTerm> {
        match tm {
            FOTerm::Var(i) => {
                if *i >= depth {
                    Some(FOTerm::Var(*i - depth))
                } else {
                    None
                }
            }
            FOTerm::Const(c) => Some(FOTerm::Const(*c)),
            FOTerm::Func { sym, args } => {
                let shifted: Option<Vec<FOTerm>> =
                    args.iter().map(|a| shift_fo_out(a, depth)).collect();
                shifted.map(|args| FOTerm::Func { sym: *sym, args })
            }
        }
    }

    fn scan_fo(tm: &FOTerm, depth: u32, pool: &mut Vec<FOTerm>, seen: &mut HashSet<FOTerm>) {
        if let Some(free_tm) = shift_fo_out(tm, depth)
            && seen.insert(free_tm.clone())
        {
            pool.push(free_tm);
        }
        if let FOTerm::Func { args, .. } = tm {
            for a in args {
                scan_fo(a, depth, pool, seen);
            }
        }
    }

    fn scan_ty(ty: &Ty, depth: u32, pool: &mut Vec<FOTerm>, seen: &mut HashSet<FOTerm>) {
        match ty {
            Ty::Pred { args, .. } => {
                for a in args {
                    scan_fo(a, depth, pool, seen);
                }
            }
            Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
                scan_ty(a, depth, pool, seen);
                scan_ty(b, depth, pool, seen);
            }
            Ty::Forall(body) | Ty::Exists(body) => scan_ty(body, depth + 1, pool, seen),
            Ty::Eq(s, t) => {
                scan_fo(s, depth, pool, seen);
                scan_fo(t, depth, pool, seen);
            }
            Ty::Atom(_) | Ty::Bot => {}
        }
    }

    let mut pool = Vec::new();
    let mut seen = HashSet::new();
    for ty in ctx.iter().chain(std::iter::once(target)) {
        scan_ty(ty, 0, &mut pool, &mut seen);
    }
    pool.sort();
    pool
}

fn collect_forall_seed_terms(ctx: &Ctx) -> Vec<(PTm, Ty)> {
    let entries = ctx_db_entries(ctx);
    let proj_pool = collect_projection_pool(ctx, 3, 96);
    let mut out = Vec::new();
    let mut seen = HashSet::<PTm>::new();

    for (tm, ty, _) in &proj_pool {
        if matches!(ty, Ty::Forall(_)) && seen.insert(tm.clone()) {
            out.push((tm.clone(), ty.clone()));
        }
    }

    let mut args_by_ty: HashMap<Ty, Vec<PTm>> = HashMap::new();
    for (tm, ty, _) in &proj_pool {
        args_by_ty.entry(ty.clone()).or_default().push(tm.clone());
    }
    for (fdb, fty) in &entries {
        if let Ty::Arr(x, y) = fty
            && matches!(y.as_ref(), Ty::Forall(_))
            && let Some(arg_terms) = args_by_ty.get(x.as_ref())
        {
            for arg_tm in arg_terms.iter().take(12) {
                let tm = PTm::App(Box::new(PTm::Var(*fdb)), Box::new(arg_tm.clone()));
                if seen.insert(tm.clone()) {
                    out.push((tm, (*y.clone())));
                }
            }
        }
    }

    out
}

fn collect_instantiated_forall_terms(
    ctx: &Ctx,
    target: &Ty,
    max_steps: usize,
    cap: usize,
) -> Vec<(PTm, Ty)> {
    if max_steps == 0 || cap == 0 {
        return Vec::new();
    }

    let witnesses = collect_witness_pool(ctx, target);
    if witnesses.is_empty() {
        return Vec::new();
    }

    let mut out = Vec::new();
    let mut seen = HashSet::<(PTm, Ty)>::new();
    let mut frontier = collect_forall_seed_terms(ctx);

    for _ in 0..max_steps {
        if frontier.is_empty() || out.len() >= cap {
            break;
        }
        let mut next = Vec::new();
        for (tm, ty) in frontier {
            let Ty::Forall(body) = ty else {
                continue;
            };
            for w in witnesses.iter().take(16) {
                let next_tm = PTm::TApp {
                    term: Box::new(tm.clone()),
                    witness: w.clone(),
                };
                let next_ty = ty_term_subst_top(w, &body);
                if seen.insert((next_tm.clone(), next_ty.clone())) {
                    if out.len() >= cap {
                        return out;
                    }
                    out.push((next_tm.clone(), next_ty.clone()));
                    next.push((next_tm, next_ty));
                }
            }
        }
        frontier = next;
    }

    out
}

fn collect_tapp_candidates(ctx: &Ctx, target: &Ty) -> Vec<(PTm, FOTerm)> {
    collect_instantiated_forall_terms(ctx, target, 3, 96)
        .into_iter()
        .filter_map(|(tm, ty)| {
            if ty != *target {
                return None;
            }
            let witness = match &tm {
                PTm::TApp { witness, .. } => witness.clone(),
                _ => return None,
            };
            Some((tm, witness))
        })
        .collect()
}

fn witness_kind_rank(tm: &FOTerm) -> u32 {
    match tm {
        FOTerm::Var(_) => 0,
        FOTerm::Const(_) => 1,
        FOTerm::Func { .. } => 2,
    }
}

fn exists_body_score(ctx: &Ctx, ty: &Ty, depth: usize) -> i64 {
    let theorem_bonus = if is_intuitionistic_theorem(ctx, ty) {
        400
    } else {
        0
    };
    if depth == 0 {
        return theorem_bonus - ty_size(ty) as i64;
    }

    match ty {
        Ty::Eq(s, t) => {
            let refl_bonus = if s == t { 200 } else { 0 };
            let tapp_bonus = (collect_tapp_candidates(ctx, ty).len() as i64) * 40;
            let rewrite_bonus = (collect_eq_rewrites(ctx, ty).len() as i64) * 12;
            let lookahead = collect_eq_rewrites(ctx, ty)
                .into_iter()
                .map(|(_, body_goal, _)| exists_body_score(ctx, &body_goal, depth - 1))
                .max()
                .unwrap_or(0);
            theorem_bonus + refl_bonus + tapp_bonus + rewrite_bonus + lookahead - ty_size(ty) as i64
        }
        Ty::Prod(a, b) => {
            theorem_bonus
                + 20
                + exists_body_score(ctx, a, depth - 1)
                + exists_body_score(ctx, b, depth - 1)
                - ty_size(ty) as i64
        }
        Ty::Sum(a, b) => {
            theorem_bonus
                + exists_body_score(ctx, a, depth - 1).max(exists_body_score(ctx, b, depth - 1))
                - ty_size(ty) as i64
        }
        Ty::Arr(a, b) => {
            let mut ext = ctx.clone();
            ext.push((**a).clone());
            theorem_bonus + exists_body_score(&ext, b, depth - 1) - ty_size(ty) as i64
        }
        Ty::Forall(body) => {
            let shifted: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
            theorem_bonus + exists_body_score(&shifted, body, depth - 1) - ty_size(ty) as i64
        }
        Ty::Exists(body) => {
            theorem_bonus + exists_body_score(ctx, body, depth - 1) - ty_size(ty) as i64
        }
        Ty::Atom(_) | Ty::Bot | Ty::Pred { .. } => theorem_bonus - ty_size(ty) as i64,
    }
}

fn rank_exists_witnesses(ctx: &Ctx, phi: &Ty, witnesses: Vec<FOTerm>) -> Vec<FOTerm> {
    let mut scored: Vec<(i64, FOTerm)> = witnesses
        .into_iter()
        .map(|w| {
            let body_ty = ty_term_subst_top(&w, phi);
            let score = exists_body_score(ctx, &body_ty, 2)
                - (fo_term_size(&w) as i64) * 120
                - (witness_kind_rank(&w) as i64) * 25;
            (score, w)
        })
        .collect();
    scored.sort_by_key(|(score, w)| (-*score, w.clone()));
    scored.into_iter().map(|(_, w)| w).collect()
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
        Ty::Atom(_) | Ty::Bot | Ty::Pred { .. } | Ty::Forall(_) | Ty::Exists(_) | Ty::Eq(_, _) => {
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
        PTm::TLam { body } => PTm::TLam {
            body: Box::new(shift_ptm_indices(d, cutoff, body)),
        },
        PTm::TApp { term, witness } => PTm::TApp {
            term: Box::new(shift_ptm_indices(d, cutoff, term)),
            witness: witness.clone(),
        },
        PTm::Pack {
            witness,
            body,
            exists_ty,
        } => PTm::Pack {
            witness: witness.clone(),
            body: Box::new(shift_ptm_indices(d, cutoff, body)),
            exists_ty: exists_ty.clone(),
        },
        PTm::Unpack { scrut, body } => PTm::Unpack {
            scrut: Box::new(shift_ptm_indices(d, cutoff, scrut)),
            body: Box::new(shift_ptm_indices(d, cutoff + 1, body)),
        },
        PTm::Refl { term } => PTm::Refl { term: term.clone() },
        PTm::Subst {
            eq_proof,
            body,
            motive,
        } => PTm::Subst {
            eq_proof: Box::new(shift_ptm_indices(d, cutoff, eq_proof)),
            body: Box::new(shift_ptm_indices(d, cutoff, body)),
            motive: motive.clone(),
        },
    }
}

pub(crate) fn scrutinee_fingerprint(scrut: &PTm, binder_depth: u32) -> u64 {
    let lifted = shift_ptm_indices(binder_depth as i32, 0, scrut);
    let mut h = std::collections::hash_map::DefaultHasher::new();
    lifted.hash(&mut h);
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
            PTm::TLam { body } => go(body, scrut, binders),
            PTm::TApp { term, .. } => go(term, scrut, binders),
            PTm::Pack { body, .. } => go(body, scrut, binders),
            PTm::Unpack { scrut: s, body } => go(s, scrut, binders) || go(body, scrut, binders + 1),
            PTm::Refl { .. } => false,
            PTm::Subst { eq_proof, body, .. } => {
                go(eq_proof, scrut, binders) || go(body, scrut, binders)
            }
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
        PTm::TLam { body } => {
            let shifted: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
            let body_ty = try_infer_ptm_type(&shifted, body)?;
            Some(Ty::Forall(Box::new(body_ty)))
        }
        PTm::TApp { term, witness } => match try_infer_ptm_type(ctx, term)? {
            Ty::Forall(body) => Some(ty_term_subst_top(witness, &body)),
            _ => None,
        },
        PTm::Pack {
            witness,
            body,
            exists_ty,
        } => match exists_ty {
            Ty::Exists(phi) => {
                let expected = ty_term_subst_top(witness, phi);
                let body_ty = try_infer_ptm_type(ctx, body)?;
                if body_ty == expected {
                    Some(exists_ty.clone())
                } else {
                    None
                }
            }
            _ => None,
        },
        PTm::Unpack { scrut, body } => match try_infer_ptm_type(ctx, scrut)? {
            Ty::Exists(phi) => {
                let shifted: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
                let mut ext = shifted;
                ext.push(*phi);
                let body_ty = try_infer_ptm_type(&ext, body)?;
                if ty_term_free_in(0, &body_ty) {
                    None
                } else {
                    Some(ty_term_shift(-1, 0, &body_ty))
                }
            }
            _ => None,
        },
        PTm::Refl { term } => Some(Ty::Eq(term.clone(), term.clone())),
        PTm::Subst {
            eq_proof,
            body,
            motive,
        } => match try_infer_ptm_type(ctx, eq_proof)? {
            Ty::Eq(lhs, rhs) => {
                let body_ty = try_infer_ptm_type(ctx, body)?;
                let expected = ty_term_subst_top(&lhs, motive);
                if body_ty == expected {
                    Some(ty_term_subst_top(&rhs, motive))
                } else {
                    None
                }
            }
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
        Ty::Forall(phi) => {
            let branch = weighted_pick(&[(0, 10), (1, policy.w_hole.max(1))], choices);
            if branch == 0 {
                let shifted_ctx: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
                let (body, ff) = synth(
                    state,
                    &shifted_ctx,
                    phi,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                return (
                    PTm::TLam {
                        body: Box::new(body),
                    },
                    ff,
                );
            }
            synth_non_arrow(
                state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
            )
        }
        Ty::Exists(phi) => {
            let mut witnesses = collect_witness_pool(ctx, target);
            if witnesses.is_empty() && !ty_term_free_in(0, phi) {
                witnesses.push(FOTerm::Const(0));
            }
            witnesses = rank_exists_witnesses(ctx, phi, witnesses);
            let can_pack = budget > 1 && !witnesses.is_empty();
            let branch = weighted_pick(
                &[
                    (0, if can_pack { 10 } else { 0 }),
                    (1, policy.w_hole.max(1)),
                ],
                choices,
            );
            if branch == 0 && can_pack {
                let w = witnesses[0].clone();
                let body_ty = ty_term_subst_top(&w, phi);
                let (body, ff) = synth_material_first(
                    state,
                    ctx,
                    &body_ty,
                    choices,
                    budget - 1,
                    allow_case,
                    policy,
                    runtime,
                    metrics,
                );
                return (
                    PTm::Pack {
                        witness: w,
                        body: Box::new(body),
                        exists_ty: target.clone(),
                    },
                    ff,
                );
            }
            synth_non_arrow(
                state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
            )
        }
        Ty::Eq(s, t) => {
            if s == t {
                return (PTm::Refl { term: s.clone() }, false);
            }
            synth_non_arrow(
                state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
            )
        }
        Ty::Atom(_) | Ty::Bot | Ty::Pred { .. } => synth_non_arrow(
            state, ctx, target, choices, budget, allow_case, policy, runtime, metrics,
        ),
    }
}

// --- Equality rewriting helpers for Subst synthesis ---

fn fo_term_replace_one(from: &FOTerm, to: &FOTerm, tm: &FOTerm) -> (FOTerm, bool) {
    if tm == from {
        return (to.clone(), true);
    }
    match tm {
        FOTerm::Func { sym, args } => {
            let mut replaced = false;
            let new_args: Vec<FOTerm> = args
                .iter()
                .map(|a| {
                    let (r, b) = fo_term_replace_one(from, to, a);
                    replaced |= b;
                    r
                })
                .collect();
            (
                FOTerm::Func {
                    sym: *sym,
                    args: new_args,
                },
                replaced,
            )
        }
        _ => (tm.clone(), false),
    }
}

fn ty_replace_fo(from: &FOTerm, to: &FOTerm, ty: &Ty) -> (Ty, bool) {
    match ty {
        Ty::Atom(_) | Ty::Bot => (ty.clone(), false),
        Ty::Pred { sym, args } => {
            let mut rep = false;
            let new_args: Vec<FOTerm> = args
                .iter()
                .map(|a| {
                    let (r, b) = fo_term_replace_one(from, to, a);
                    rep |= b;
                    r
                })
                .collect();
            (
                Ty::Pred {
                    sym: *sym,
                    args: new_args,
                },
                rep,
            )
        }
        Ty::Eq(s, t) => {
            let (s2, b1) = fo_term_replace_one(from, to, s);
            let (t2, b2) = fo_term_replace_one(from, to, t);
            (Ty::Eq(s2, t2), b1 || b2)
        }
        Ty::Arr(a, b) => {
            let (a2, b1) = ty_replace_fo(from, to, a);
            let (b2, b2r) = ty_replace_fo(from, to, b);
            (Ty::Arr(Box::new(a2), Box::new(b2)), b1 || b2r)
        }
        Ty::Prod(a, b) => {
            let (a2, b1) = ty_replace_fo(from, to, a);
            let (b2, b2r) = ty_replace_fo(from, to, b);
            (Ty::Prod(Box::new(a2), Box::new(b2)), b1 || b2r)
        }
        Ty::Sum(a, b) => {
            let (a2, b1) = ty_replace_fo(from, to, a);
            let (b2, b2r) = ty_replace_fo(from, to, b);
            (Ty::Sum(Box::new(a2), Box::new(b2)), b1 || b2r)
        }
        Ty::Forall(_) | Ty::Exists(_) => (ty.clone(), false),
    }
}

/// Compute motive φ such that φ[rhs/0] = goal, by abstracting `rhs` from `goal`.
fn try_make_motive(rhs: &FOTerm, goal: &Ty) -> Option<Ty> {
    let shifted_goal = ty_term_shift(1, 0, goal);
    let shifted_rhs = fo_term_shift(1, 0, rhs);
    let (motive, replaced) = ty_replace_fo(&shifted_rhs, &FOTerm::Var(0), &shifted_goal);
    if replaced { Some(motive) } else { None }
}

/// For each Eq(lhs, rhs) in ctx where rhs appears in goal, yield (eq_var, body_goal, motive).
fn collect_eq_rewrites(ctx: &Ctx, goal: &Ty) -> Vec<(PTm, Ty, Ty)> {
    let mut out = Vec::new();
    let mut push_rewrite = |proof: PTm, lhs: FOTerm, rhs: FOTerm| {
        if let Some(motive) = try_make_motive(&rhs, goal) {
            let body_goal = ty_term_subst_top(&lhs, &motive);
            out.push((proof.clone(), body_goal, motive));
        }
        if let Some(motive) = try_make_motive(&lhs, goal) {
            let body_goal = ty_term_subst_top(&rhs, &motive);
            out.push((proof, body_goal, motive));
        }
    };

    for (db, ty) in ctx_db_entries(ctx) {
        if let Ty::Eq(lhs, rhs) = ty {
            push_rewrite(PTm::Var(db), lhs, rhs);
        }
    }

    for (tm, ty) in collect_instantiated_forall_terms(ctx, goal, 3, 96) {
        if let Ty::Eq(lhs, rhs) = ty {
            push_rewrite(tm, lhs, rhs);
        }
    }
    out.sort_by_key(|(proof, body_goal, motive)| {
        (ty_size(body_goal), ptm_size(proof), ty_size(motive))
    });
    out.dedup_by(|a, b| a.1 == b.1 && a.2 == b.2);
    out.truncate(6);
    out
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
    let unpack_scruts = collect_unpack_scrutinees(ctx);
    let can_unpack = budget > 1 && !unpack_scruts.is_empty();
    let tapp_cands = collect_tapp_candidates(ctx, target);
    let can_tapp = budget > 1 && !tapp_cands.is_empty();
    let eq_rewrites = collect_eq_rewrites(ctx, target);
    let can_subst = budget > 1 && !eq_rewrites.is_empty();
    let allow_absurd = budget > 1
        && target != &Ty::Bot
        && (!matches!(target, Ty::Eq(_, _)) || (!can_subst && !can_tapp));

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
    if allow_absurd {
        options.push((4, policy.w_absurd.max(1)));
    }
    if can_case {
        options.push((5, policy.w_case.max(1)));
    }
    if can_unpack {
        options.push((7, policy.w_case.max(1)));
    }
    if can_tapp {
        options.push((8, policy.w_direct_app.max(1)));
    }
    if can_subst {
        options.push((9, policy.w_app.max(1)));
    }
    options.push((3, policy.w_hole.max(1)));

    let only_hole = options.len() == 1 && options[0].0 == 3;
    let pick = weighted_pick(&options, choices);
    let (tm, ff) = match pick {
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
        7 => {
            if unpack_scruts.is_empty() {
                return (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                );
            }
            let pick = (choices.next_u32() as usize) % unpack_scruts.len();
            let scrut = unpack_scruts[pick].clone();
            let scrut_ty = match try_infer_ptm_type(ctx, &scrut) {
                Some(t) => t,
                None => {
                    return (
                        state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                        false,
                    );
                }
            };
            let phi = match scrut_ty {
                Ty::Exists(phi) => *phi,
                _ => {
                    return (
                        state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                        false,
                    );
                }
            };

            let scale = policy.branch_budget_scale_per_mille.clamp(200, 1000);
            let branch_budget = (((budget - 1) as u64 * scale as u64) / 1000).max(1) as u32;

            // Unpack binds: shift ctx for term var, push φ as proof var
            let shifted_ctx: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
            let mut ext = shifted_ctx;
            ext.push(phi.clone());

            let bp = branch_policy(policy, &phi, target);
            let (body, ff) = synth(
                state,
                &ext,
                target,
                choices,
                branch_budget,
                true,
                &bp,
                runtime,
                metrics,
            );
            (
                PTm::Unpack {
                    scrut: Box::new(scrut),
                    body: Box::new(body),
                },
                ff,
            )
        }
        8 => {
            if tapp_cands.is_empty() {
                return (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                );
            }
            let pick = (choices.next_u32() as usize) % tapp_cands.len();
            let (term, witness) = tapp_cands[pick].clone();
            (
                PTm::TApp {
                    term: Box::new(term),
                    witness,
                },
                false,
            )
        }
        9 => {
            if eq_rewrites.is_empty() {
                return (
                    state.fresh_hole(ctx.clone(), target.clone(), allow_case),
                    false,
                );
            }
            let pick = (choices.next_u32() as usize) % eq_rewrites.len();
            let (eq_proof, body_goal, motive) = eq_rewrites[pick].clone();
            let scale = policy.branch_budget_scale_per_mille.clamp(200, 1000);
            let branch_budget = (((budget - 1) as u64 * scale as u64) / 1000).max(1) as u32;
            let bp = branch_policy(policy, &body_goal, target);
            let (body, ff) = synth(
                state,
                ctx,
                &body_goal,
                choices,
                branch_budget,
                allow_case,
                &bp,
                runtime,
                metrics,
            );
            (
                PTm::Subst {
                    eq_proof: Box::new(eq_proof),
                    body: Box::new(body),
                    motive,
                },
                ff,
            )
        }
        _ => (
            state.fresh_hole(ctx.clone(), target.clone(), allow_case),
            only_hole,
        ),
    };
    // Only propagate forced_fail when there were no other options (only_hole).
    // If multiple options existed and the chosen path failed, it doesn't mean
    // the goal is unprovable — a different option might succeed. Memoizing as
    // Failed in that case would permanently block valid solution paths.
    (tm, ff && only_hole)
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
            PTm::TLam { body } => go(body, hole_id, payload),
            PTm::TApp { term, .. } => go(term, hole_id, payload),
            PTm::Pack { body, .. } => go(body, hole_id, payload),
            PTm::Unpack { scrut, body } => {
                go(scrut, hole_id, payload) || go(body, hole_id, payload)
            }
            PTm::Refl { .. } => false,
            PTm::Subst { eq_proof, body, .. } => {
                go(eq_proof, hole_id, payload) || go(body, hole_id, payload)
            }
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
        Ty::Eq(s, t) if s == t => {
            push(PTm::Refl { term: s.clone() }, &mut out, &mut seen);
        }
        Ty::Atom(_) | Ty::Bot | Ty::Forall(_) | Ty::Exists(_) | Ty::Pred { .. } | Ty::Eq(_, _) => {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ga::corpus::arith_corpus;

    fn zero() -> FOTerm {
        FOTerm::Const(0)
    }

    fn succ(x: FOTerm) -> FOTerm {
        FOTerm::Func {
            sym: 0,
            args: vec![x],
        }
    }

    fn add(x: FOTerm, y: FOTerm) -> FOTerm {
        FOTerm::Func {
            sym: 1,
            args: vec![x, y],
        }
    }

    #[test]
    fn collect_instantiated_forall_terms_handle_nested_forall_instantiation() {
        let case = arith_corpus()
            .into_iter()
            .find(|c| c.name == "C2_AddOne")
            .expect("C2_AddOne exists");
        let Ty::Forall(goal) = case.target else {
            panic!("C2_AddOne should be forall");
        };
        let shifted_ctx: Ctx = case.ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();

        let expected = Ty::Eq(
            add(FOTerm::Var(0), succ(zero())),
            succ(add(FOTerm::Var(0), zero())),
        );

        let instantiated = collect_instantiated_forall_terms(&shifted_ctx, &goal, 3, 96);
        assert!(
            instantiated.iter().any(|(tm, ty)| {
                matches!(
                    tm,
                    PTm::TApp { term, .. } if matches!(term.as_ref(), PTm::TApp { .. })
                ) && *ty == expected
            }),
            "expected nested TApp instantiation for ax_add_succ[x][0]"
        );
    }

    #[test]
    fn collect_eq_rewrites_stage_c2_addone_via_instantiated_equalities() {
        let case = arith_corpus()
            .into_iter()
            .find(|c| c.name == "C2_AddOne")
            .expect("C2_AddOne exists");
        let Ty::Forall(goal) = case.target else {
            panic!("C2_AddOne should be forall");
        };
        let shifted_ctx: Ctx = case.ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();

        let expected_body_goal = Ty::Eq(succ(add(FOTerm::Var(0), zero())), succ(FOTerm::Var(0)));
        let rewrites = collect_eq_rewrites(&shifted_ctx, &goal);
        assert!(
            rewrites.iter().any(|(proof, body_goal, _)| {
                matches!(
                    proof,
                    PTm::TApp { term, .. } if matches!(term.as_ref(), PTm::TApp { .. })
                ) && *body_goal == expected_body_goal
            }),
            "expected first rewrite step to use instantiated ax_add_succ"
        );
    }

    #[test]
    fn rank_exists_witnesses_prioritizes_var_for_c4_exists_addone() {
        let case = arith_corpus()
            .into_iter()
            .find(|c| c.name == "C4_ExistsAddOne")
            .expect("C4_ExistsAddOne exists");
        let Ty::Forall(target) = case.target else {
            panic!("C4_ExistsAddOne should be forall");
        };
        let shifted_ctx: Ctx = case.ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
        let Ty::Exists(phi) = *target else {
            panic!("inner goal should be exists");
        };
        let witnesses = collect_witness_pool(&shifted_ctx, &Ty::Exists(phi.clone()));
        let ranked = rank_exists_witnesses(&shifted_ctx, &phi, witnesses);
        assert_eq!(ranked.first(), Some(&FOTerm::Var(0)));
    }

    #[test]
    fn rank_exists_witnesses_prioritizes_var_for_b5_exists_prod() {
        let case = arith_corpus()
            .into_iter()
            .find(|c| c.name == "B5_ExistsProd")
            .expect("B5_ExistsProd exists");
        let Ty::Forall(target) = case.target else {
            panic!("B5_ExistsProd should be forall");
        };
        let shifted_ctx: Ctx = case.ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
        let Ty::Exists(phi) = *target else {
            panic!("inner goal should be exists");
        };
        let witnesses = collect_witness_pool(&shifted_ctx, &Ty::Exists(phi.clone()));
        let ranked = rank_exists_witnesses(&shifted_ctx, &phi, witnesses);
        assert_eq!(ranked.first(), Some(&FOTerm::Var(0)));
    }
}
