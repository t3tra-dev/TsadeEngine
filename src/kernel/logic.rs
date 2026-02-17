use super::{Ctx, Ty};

fn normalize_ctx(ctx: &Ctx) -> Ctx {
    fn push_flat(ty: &Ty, out: &mut Ctx) {
        match ty {
            Ty::Prod(a, b) => {
                push_flat(a, out);
                push_flat(b, out);
            }
            _ => out.push(ty.clone()),
        }
    }

    let mut flat = Vec::new();
    for t in ctx {
        push_flat(t, &mut flat);
    }
    flat.sort();
    flat.dedup();
    flat
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct Sequent {
    ctx: Ctx,
    goal: Ty,
}

fn decide_inner(
    ctx: &Ctx,
    goal: &Ty,
    visiting: &mut std::collections::HashSet<Sequent>,
    memo: &mut std::collections::HashMap<Sequent, bool>,
) -> bool {
    let key = Sequent {
        ctx: normalize_ctx(ctx),
        goal: goal.clone(),
    };
    if let Some(v) = memo.get(&key) {
        return *v;
    }
    if !visiting.insert(key.clone()) {
        return false;
    }

    if key.ctx.contains(goal) {
        visiting.remove(&key);
        memo.insert(key, true);
        return true;
    }
    if key.ctx.contains(&Ty::Bot) {
        visiting.remove(&key);
        memo.insert(key, true);
        return true;
    }

    for (i, cty) in key.ctx.iter().enumerate() {
        if let Ty::Sum(a, b) = cty {
            let mut lctx = key.ctx.clone();
            lctx.remove(i);
            lctx.push((**a).clone());
            let mut rctx = key.ctx.clone();
            rctx.remove(i);
            rctx.push((**b).clone());
            if decide_inner(&lctx, goal, visiting, memo)
                && decide_inner(&rctx, goal, visiting, memo)
            {
                visiting.remove(&key);
                memo.insert(key, true);
                return true;
            }
        }
    }

    let result = match goal {
        Ty::Prod(a, b) => {
            decide_inner(&key.ctx, a, visiting, memo) && decide_inner(&key.ctx, b, visiting, memo)
        }
        Ty::Sum(a, b) => {
            decide_inner(&key.ctx, a, visiting, memo) || decide_inner(&key.ctx, b, visiting, memo)
        }
        Ty::Arr(a, b) => {
            let mut ext = key.ctx.clone();
            ext.push((**a).clone());
            decide_inner(&ext, b, visiting, memo)
        }
        Ty::Atom(_) | Ty::Bot => {
            let mut ok = false;
            for f in &key.ctx {
                if let Ty::Arr(a, b) = f {
                    if !decide_inner(&key.ctx, a, visiting, memo) {
                        continue;
                    }
                    let mut ext = key.ctx.clone();
                    ext.push((**b).clone());
                    if decide_inner(&ext, goal, visiting, memo) {
                        ok = true;
                        break;
                    }
                }
            }
            ok
        }
    };

    visiting.remove(&key);
    memo.insert(key, result);
    result
}

pub fn is_intuitionistic_theorem(ctx: &Ctx, goal: &Ty) -> bool {
    let mut visiting = std::collections::HashSet::new();
    let mut memo = std::collections::HashMap::new();
    decide_inner(ctx, goal, &mut visiting, &mut memo)
}

#[derive(Clone, Debug)]
pub struct KripkeCounterModel {
    pub worlds: usize,
    pub witness_world: usize,
    pub leq: Vec<Vec<bool>>,
    pub valuation: Vec<Vec<u32>>,
}

fn collect_atoms(ty: &Ty, out: &mut std::collections::BTreeSet<u32>) {
    match ty {
        Ty::Atom(i) => {
            out.insert(*i);
        }
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            collect_atoms(a, out);
            collect_atoms(b, out);
        }
        Ty::Bot => {}
    }
}

fn kripke_forces(
    model: &KripkeCounterModel,
    w: usize,
    ty: &Ty,
    memo: &mut std::collections::HashMap<(usize, Ty), bool>,
) -> bool {
    let key = (w, ty.clone());
    if let Some(v) = memo.get(&key) {
        return *v;
    }

    let ans = match ty {
        Ty::Atom(i) => model.valuation[w].contains(i),
        Ty::Bot => false,
        Ty::Prod(a, b) => kripke_forces(model, w, a, memo) && kripke_forces(model, w, b, memo),
        Ty::Sum(a, b) => kripke_forces(model, w, a, memo) || kripke_forces(model, w, b, memo),
        Ty::Arr(a, b) => (0..model.worlds)
            .filter(|v| model.leq[w][*v])
            .all(|v| !kripke_forces(model, v, a, memo) || kripke_forces(model, v, b, memo)),
    };
    memo.insert(key, ans);
    ans
}

fn enumerate_posets(worlds: usize) -> Vec<Vec<Vec<bool>>> {
    if worlds == 0 {
        return vec![];
    }
    let mut pairs = Vec::new();
    for i in 0..worlds {
        for j in (i + 1)..worlds {
            pairs.push((i, j));
        }
    }
    let mut out = Vec::new();
    let total = 1usize << pairs.len();
    for mask in 0..total {
        let mut leq = vec![vec![false; worlds]; worlds];
        for (i, row) in leq.iter_mut().enumerate().take(worlds) {
            row[i] = true;
        }
        for (bit, (i, j)) in pairs.iter().enumerate() {
            if ((mask >> bit) & 1) == 1 {
                leq[*i][*j] = true;
            }
        }
        let mut transitive = true;
        for i in 0..worlds {
            for j in 0..worlds {
                for k in 0..worlds {
                    if leq[i][j] && leq[j][k] && !leq[i][k] {
                        transitive = false;
                        break;
                    }
                }
                if !transitive {
                    break;
                }
            }
            if !transitive {
                break;
            }
        }
        if transitive {
            out.push(leq);
        }
    }
    out
}

fn enumerate_upsets(leq: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let n = leq.len();
    let mut out = Vec::new();
    let total = 1usize << n;
    'mask_loop: for mask in 0..total {
        let mut s = vec![false; n];
        for (i, slot) in s.iter_mut().enumerate().take(n) {
            *slot = ((mask >> i) & 1) == 1;
        }
        for i in 0..n {
            if !s[i] {
                continue;
            }
            for (j, present) in s.iter().enumerate().take(n) {
                if leq[i][j] && !*present {
                    continue 'mask_loop;
                }
            }
        }
        out.push(s);
    }
    out
}

fn enumerate_monotone_valuations_for_poset(
    atoms: &[u32],
    leq: &[Vec<bool>],
    out: &mut Vec<Vec<Vec<u32>>>,
) {
    let n = leq.len();
    let upsets = enumerate_upsets(leq);
    let mut picks = vec![0usize; atoms.len()];

    fn go(
        atoms: &[u32],
        n: usize,
        upsets: &[Vec<bool>],
        picks: &mut [usize],
        idx: usize,
        out: &mut Vec<Vec<Vec<u32>>>,
    ) {
        if idx == atoms.len() {
            let mut valuation = vec![Vec::<u32>::new(); n];
            for (ai, atom) in atoms.iter().enumerate() {
                let up = &upsets[picks[ai]];
                for w in 0..n {
                    if up[w] {
                        valuation[w].push(*atom);
                    }
                }
            }
            out.push(valuation);
            return;
        }
        for i in 0..upsets.len() {
            picks[idx] = i;
            go(atoms, n, upsets, picks, idx + 1, out);
        }
    }

    go(atoms, n, &upsets, &mut picks, 0, out);
}

pub fn find_kripke_countermodel(
    ctx: &Ctx,
    goal: &Ty,
    max_worlds: usize,
) -> Option<KripkeCounterModel> {
    let mut atoms = std::collections::BTreeSet::new();
    for t in ctx {
        collect_atoms(t, &mut atoms);
    }
    collect_atoms(goal, &mut atoms);
    let atoms: Vec<u32> = atoms.into_iter().collect();

    for worlds in 1..=max_worlds.max(1) {
        let posets = enumerate_posets(worlds);
        for leq in posets {
            let mut all_vals = Vec::new();
            enumerate_monotone_valuations_for_poset(&atoms, &leq, &mut all_vals);
            for valuation in all_vals {
                let model = KripkeCounterModel {
                    worlds,
                    witness_world: 0,
                    leq: leq.clone(),
                    valuation,
                };
                for w in 0..worlds {
                    let mut memo = std::collections::HashMap::new();
                    let ctx_true = ctx.iter().all(|t| kripke_forces(&model, w, t, &mut memo));
                    let goal_true = kripke_forces(&model, w, goal, &mut memo);
                    if ctx_true && !goal_true {
                        let mut hit = model.clone();
                        hit.witness_world = w;
                        return Some(hit);
                    }
                }
            }
        }
    }
    None
}
