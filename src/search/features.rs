use super::{Goal, PTm, PartialFeatures, SearchState};
use crate::kernel::{Ty, fo_term_size, ty_size};

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
            PTm::TLam { body } => go(body, pred),
            PTm::TApp { term, .. } => go(term, pred),
            PTm::Pack { body, .. } => go(body, pred),
            PTm::Unpack { scrut, body } => go(scrut, pred) + go(body, pred),
            PTm::Refl { .. } => 0,
            PTm::Subst { eq_proof, body, .. } => go(eq_proof, pred) + go(body, pred),
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

pub fn ptm_tlam_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::TLam { .. })))
}

pub fn ptm_pack_nodes(tm: &PTm) -> usize {
    count_nodes(tm, |n| usize::from(matches!(n, PTm::Pack { .. })))
}

/// Pack/TApp ノードの witness FOTerm サイズを合計する。
/// 大きな witness (S(S(S(0))) 等) にコストをかけて偏らせる。
pub fn ptm_fo_witness_cost(tm: &PTm) -> usize {
    count_nodes(tm, |n| match n {
        PTm::Pack { witness, .. } => fo_term_size(witness),
        PTm::TApp { witness, .. } => fo_term_size(witness),
        _ => 0,
    })
}

/// ゴールが synth でどれほど解きやすいかを推定する軽量スコア。
///
/// 0 = 明らかに詰まっている（⊥ で ctx に助けなし、等）
/// > 0 = 何らかの構造的手または仮定が使える
///
/// 型に特化した special-case をしない: 構造的導入規則・ctx 中の
/// 型マッチ・消去規則の有無だけを速いループで見る。
fn goal_tractability(goal: &Goal) -> u32 {
    let ctx = &goal.ctx;
    let ty = &goal.ty;
    let mut score = 0u32;

    // Refl で即閉じられる
    if let Ty::Eq(s, t) = ty
        && s == t
    {
        return 10;
    }

    // 構造的導入規則が常に使える型
    match ty {
        Ty::Arr(_, _) | Ty::Forall(_) => score += 4,
        Ty::Prod(_, _) => score += 3,
        Ty::Exists(_) => score += 2,
        _ => {}
    }

    // Bot ゴールは特別扱い: ctx の Ty::Bot は TLam のプレースホルダーであり
    // 本物の ⊥ 仮定ではないため、通常の Var マッチを適用してはならない。
    // 成立条件は否定除去 (A と A→⊥ が ctx にある) のみ。
    if matches!(ty, Ty::Bot) {
        for t in ctx {
            if let Ty::Arr(a, b) = t
                && matches!(b.as_ref(), Ty::Bot)
                && ctx.contains(a.as_ref())
            {
                return 4;
            }
        }
        return 0; // 詰まり確定
    }

    // ctx に同型の Var がある (直接 Var で閉じられる)
    // Bot は上で処理済みなのでここでは Var マッチから除外しなくてよい
    if ctx.iter().any(|t| t == ty) {
        score += 5;
    }

    // ctx の Arr で結果型が ty に一致 (App で閉じられる)
    if ctx.iter().any(|t| {
        if let Ty::Arr(_, b) = t {
            b.as_ref() == ty
        } else {
            false
        }
    }) {
        score += 4;
    }

    // Eq ゴール向け: ctx に Eq 仮定や ∀ 仮定があれば Subst/TApp が使える
    if matches!(ty, Ty::Eq(_, _)) {
        if ctx.iter().any(|t| matches!(t, Ty::Eq(_, _))) {
            score += 3;
        }
        if ctx.iter().any(|t| matches!(t, Ty::Forall(_))) {
            score += 1;
        }
    }

    // Sum が ctx にあれば Case 消去が使える可能性
    if ctx.iter().any(|t| matches!(t, Ty::Sum(_, _))) {
        score += 1;
    }

    score
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
            PTm::TLam { body } => go(body, ancestors, binders),
            PTm::TApp { term, .. } => go(term, ancestors, binders),
            PTm::Pack { body, .. } => go(body, ancestors, binders),
            PTm::Unpack { scrut, body } => {
                go(scrut, ancestors, binders) + go(body, ancestors, binders + 1)
            }
            PTm::Refl { .. } => 0,
            PTm::Subst { eq_proof, body, .. } => {
                go(eq_proof, ancestors, binders) + go(body, ancestors, binders)
            }
            PTm::Hole { .. } | PTm::Var(_) => 0,
        }
    }
    let mut anc = Vec::new();
    go(tm, &mut anc, 0)
}

pub fn partial_features(state: &SearchState) -> PartialFeatures {
    let tractabilities: Vec<u32> = state.goals.values().map(goal_tractability).collect();
    let stuck_goals = tractabilities.iter().filter(|&&t| t == 0).count();
    let total_tractability = tractabilities.iter().map(|&t| t as usize).sum();
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
        tlam_nodes: ptm_tlam_nodes(&state.root),
        pack_nodes: ptm_pack_nodes(&state.root),
        fo_witness_cost: ptm_fo_witness_cost(&state.root),
        stuck_goals,
        total_tractability,
    }
}

pub fn score_partial(state: &SearchState) -> i64 {
    let f = partial_features(state);
    if f.holes == 0 {
        return 1_000_000
            - (f.root_size as i64)
            - (f.app_nodes as i64 * 2)
            - (f.case_nodes as i64 * 4)
            - (f.repeat_case_nodes as i64 * 20)
            - (f.fo_witness_cost as i64 * 3);
    }
    let holes = f.holes as i64;
    let goal_c = f.goal_complexity as i64;

    // close_bonus: tractable なゴールが残っている場合のみ有効にする。
    // 全ゴールが stuck (tractability == 0) の場合は 0 — 詰まった状態を
    // 「ゴールが小さい」という理由で良く見せる誤誘導を防ぐ。
    let close_bonus = if f.stuck_goals >= f.holes {
        0
    } else {
        let active = (f.holes - f.stuck_goals) as i64;
        3000 / (active + 1) + 1200 / (goal_c + 1)
    };

    let intro_progress = (f.pair_nodes.min(4) as i64) * 30
        + (f.sum_intro_nodes.min(4) as i64) * 40
        + (f.proj_nodes.min(6) as i64) * 20
        + (f.tlam_nodes.min(4) as i64) * 25
        + (f.pack_nodes.min(4) as i64) * 30;

    // tractability ボーナス: 残りゴールが解きやすいほど小さな加点
    let tractability_bonus = (f.total_tractability.min(30) as i64) * 12;

    -((holes) * 1800
        + (holes * holes) * 220
        + (goal_c) * 55
        + (f.root_size as i64) * 3
        + (f.app_nodes as i64) * 10
        + (f.case_nodes as i64) * 8
        + (f.repeat_case_nodes as i64) * 30
        + (f.fo_witness_cost as i64) * 8
        + (f.stuck_goals as i64) * 900)       // 詰まったゴールへの強いペナルティ
        + intro_progress
        + tractability_bonus
        + close_bonus
}
