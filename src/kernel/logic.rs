use super::{Ctx, FOTerm, Ty, fo_term_size, ty_term_shift, ty_term_subst_top};

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
        Ty::Pred { .. } | Ty::Forall(_) | Ty::Exists(_) | Ty::Eq(_, _) => false,
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

fn is_propositional(ty: &Ty) -> bool {
    match ty {
        Ty::Atom(_) | Ty::Bot => true,
        Ty::Pred { .. } | Ty::Forall(_) | Ty::Exists(_) | Ty::Eq(_, _) => false,
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            is_propositional(a) && is_propositional(b)
        }
    }
}

fn collect_consts_fo(tm: &FOTerm, out: &mut std::collections::BTreeSet<u32>) {
    match tm {
        FOTerm::Var(_) => {}
        FOTerm::Const(c) => {
            out.insert(*c);
        }
        FOTerm::Func { args, .. } => {
            for a in args {
                collect_consts_fo(a, out);
            }
        }
    }
}

fn collect_consts_ty(ty: &Ty, out: &mut std::collections::BTreeSet<u32>) {
    match ty {
        Ty::Atom(_) | Ty::Bot => {}
        Ty::Pred { args, .. } => {
            for a in args {
                collect_consts_fo(a, out);
            }
        }
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            collect_consts_ty(a, out);
            collect_consts_ty(b, out);
        }
        Ty::Forall(body) | Ty::Exists(body) => {
            collect_consts_ty(body, out);
        }
        Ty::Eq(s, t) => {
            collect_consts_fo(s, out);
            collect_consts_fo(t, out);
        }
    }
}

/// Structurally replace every occurrence of `from` inside `tm` with `to`.
/// FOTerms have no binders, so this is straightforward structural recursion.
fn fo_replace(from: &FOTerm, to: &FOTerm, tm: &FOTerm) -> FOTerm {
    if tm == from {
        return to.clone();
    }
    match tm {
        FOTerm::Func { sym, args } => FOTerm::Func {
            sym: *sym,
            args: args.iter().map(|a| fo_replace(from, to, a)).collect(),
        },
        _ => tm.clone(),
    }
}

fn collect_subterms_fo(tm: &FOTerm, max_size: usize, out: &mut std::collections::BTreeSet<FOTerm>) {
    if fo_term_size(tm) <= max_size {
        out.insert(tm.clone());
    }
    if let FOTerm::Func { args, .. } = tm {
        for a in args {
            collect_subterms_fo(a, max_size, out);
        }
    }
}

fn collect_subterms_ty(ty: &Ty, max_size: usize, out: &mut std::collections::BTreeSet<FOTerm>) {
    match ty {
        Ty::Atom(_) | Ty::Bot => {}
        Ty::Pred { args, .. } => {
            for a in args {
                collect_subterms_fo(a, max_size, out);
            }
        }
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            collect_subterms_ty(a, max_size, out);
            collect_subterms_ty(b, max_size, out);
        }
        Ty::Forall(body) | Ty::Exists(body) => {
            collect_subterms_ty(body, max_size, out);
        }
        Ty::Eq(s, t) => {
            collect_subterms_fo(s, max_size, out);
            collect_subterms_fo(t, max_size, out);
        }
    }
}

fn fol_available_terms(ctx: &Ctx, goal: &Ty, term_depth: u32) -> Vec<FOTerm> {
    // Herbrand universe: de Bruijn term variables + Const values from ctx/goal
    // + structural subterms already appearing in the goal.
    // We avoid harvesting function terms from ctx because recursive calls see
    // saturated contexts; doing so makes the term universe grow aggressively.
    let mut consts = std::collections::BTreeSet::new();
    for t in ctx {
        collect_consts_ty(t, &mut consts);
    }
    collect_consts_ty(goal, &mut consts);
    let mut terms = std::collections::BTreeSet::new();
    for i in 0..term_depth {
        terms.insert(FOTerm::Var(i));
    }
    for c in consts {
        terms.insert(FOTerm::Const(c));
    }
    collect_subterms_ty(goal, 3, &mut terms);
    terms.into_iter().collect()
}

fn fol_saturate_forall(mut ctx: Ctx, terms: &[FOTerm]) -> Ctx {
    if terms.is_empty() {
        return ctx;
    }
    loop {
        let mut added = false;
        let n = ctx.len();
        for i in 0..n {
            if let Ty::Forall(phi) = ctx[i].clone() {
                for w in terms {
                    let inst = ty_term_subst_top(w, &phi);
                    if !ctx.contains(&inst) {
                        ctx.push(inst);
                        added = true;
                    }
                }
            }
        }
        if !added {
            break;
        }
    }
    ctx
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct FolSequent {
    ctx: Ctx,
    goal: Ty,
    term_depth: u32,
}

fn decide_fol_inner(
    ctx: &Ctx,
    goal: &Ty,
    term_depth: u32,
    depth_limit: u32,
    visiting: &mut std::collections::HashSet<FolSequent>,
    memo: &mut std::collections::HashMap<FolSequent, bool>,
) -> bool {
    if depth_limit == 0 {
        return false;
    }
    let mut norm = ctx.clone();
    norm.sort();
    norm.dedup();
    let key = FolSequent {
        ctx: norm,
        goal: goal.clone(),
        term_depth,
    };
    if let Some(v) = memo.get(&key) {
        return *v;
    }
    if !visiting.insert(key.clone()) {
        return false;
    }
    let result = decide_fol_work(&key.ctx, goal, term_depth, depth_limit - 1, visiting, memo);
    visiting.remove(&key);
    memo.insert(key, result);
    result
}

fn decide_fol_work(
    ctx: &Ctx,
    goal: &Ty,
    term_depth: u32,
    depth_limit: u32,
    visiting: &mut std::collections::HashSet<FolSequent>,
    memo: &mut std::collections::HashMap<FolSequent, bool>,
) -> bool {
    if ctx.contains(goal) {
        return true;
    }
    if ctx.contains(&Ty::Bot) {
        return true;
    }

    // ∀-L: saturate context with all Forall instantiations at the Herbrand universe
    let terms = fol_available_terms(ctx, goal, term_depth);
    let ctx = fol_saturate_forall(ctx.clone(), &terms);

    if ctx.contains(goal) {
        return true;
    }
    if ctx.contains(&Ty::Bot) {
        return true;
    }

    // ∃-L: eigenvariable rule for each ∃ in ctx
    for i in 0..ctx.len() {
        if let Ty::Exists(phi) = ctx[i].clone() {
            let mut new_ctx: Ctx = ctx
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, t)| ty_term_shift(1, 0, t))
                .collect();
            new_ctx.push(*phi);
            let new_goal = ty_term_shift(1, 0, goal);
            if decide_fol_inner(
                &new_ctx,
                &new_goal,
                term_depth + 1,
                depth_limit,
                visiting,
                memo,
            ) {
                return true;
            }
        }
    }

    // Sum-L: case split on ∨ in ctx
    for i in 0..ctx.len() {
        if let Ty::Sum(a, b) = ctx[i].clone() {
            let mut lctx = ctx.clone();
            lctx.remove(i);
            lctx.push(*a);
            let mut rctx = ctx.clone();
            rctx.remove(i);
            rctx.push(*b);
            if decide_fol_inner(&lctx, goal, term_depth, depth_limit, visiting, memo)
                && decide_fol_inner(&rctx, goal, term_depth, depth_limit, visiting, memo)
            {
                return true;
            }
        }
    }

    match goal {
        Ty::Prod(a, b) => {
            decide_fol_inner(&ctx, a, term_depth, depth_limit, visiting, memo)
                && decide_fol_inner(&ctx, b, term_depth, depth_limit, visiting, memo)
        }
        Ty::Sum(a, b) => {
            decide_fol_inner(&ctx, a, term_depth, depth_limit, visiting, memo)
                || decide_fol_inner(&ctx, b, term_depth, depth_limit, visiting, memo)
        }
        Ty::Arr(a, b) => {
            let mut ext = ctx.clone();
            ext.push((**a).clone());
            decide_fol_inner(&ext, b, term_depth, depth_limit, visiting, memo)
        }
        Ty::Forall(phi) => {
            // ∀-R: introduce fresh term variable (de Bruijn shift)
            let shifted: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
            decide_fol_inner(&shifted, phi, term_depth + 1, depth_limit, visiting, memo)
        }
        Ty::Exists(phi) => {
            // ∃-R: try each available witness
            for w in &terms {
                let inst = ty_term_subst_top(w, phi);
                if decide_fol_inner(&ctx, &inst, term_depth, depth_limit, visiting, memo) {
                    return true;
                }
            }
            false
        }
        Ty::Eq(s, t) => {
            if s == t {
                return true;
            }
            // Eq-L: paramodulation — rewrite s or t using lhs→rhs of each Eq hypothesis.
            // Only lhs→rhs (never rhs→lhs) keeps the terms non-growing and prevents
            // looping on unprovable goals.
            for h in ctx.clone() {
                if let Ty::Eq(u, v) = &h {
                    let new_s = fo_replace(u, v, s);
                    if &new_s != s
                        && decide_fol_inner(
                            &ctx,
                            &Ty::Eq(new_s, t.clone()),
                            term_depth,
                            depth_limit,
                            visiting,
                            memo,
                        )
                    {
                        return true;
                    }
                    let new_t = fo_replace(u, v, t);
                    if &new_t != t
                        && decide_fol_inner(
                            &ctx,
                            &Ty::Eq(s.clone(), new_t),
                            term_depth,
                            depth_limit,
                            visiting,
                            memo,
                        )
                    {
                        return true;
                    }
                }
            }
            // Arrow-L fallback
            for f in &ctx {
                if let Ty::Arr(a, b) = f {
                    if !decide_fol_inner(&ctx, a, term_depth, depth_limit, visiting, memo) {
                        continue;
                    }
                    let mut ext = ctx.clone();
                    ext.push((**b).clone());
                    if decide_fol_inner(&ext, goal, term_depth, depth_limit, visiting, memo) {
                        return true;
                    }
                }
            }
            false
        }
        Ty::Atom(_) | Ty::Pred { .. } | Ty::Bot => {
            // Arrow-L: use implications in ctx to derive atomic goal
            for f in &ctx {
                if let Ty::Arr(a, b) = f {
                    if !decide_fol_inner(&ctx, a, term_depth, depth_limit, visiting, memo) {
                        continue;
                    }
                    let mut ext = ctx.clone();
                    ext.push((**b).clone());
                    if decide_fol_inner(&ext, goal, term_depth, depth_limit, visiting, memo) {
                        return true;
                    }
                }
            }
            false
        }
    }
}

pub fn is_intuitionistic_theorem(ctx: &Ctx, goal: &Ty) -> bool {
    if is_propositional(goal) && ctx.iter().all(is_propositional) {
        let mut visiting = std::collections::HashSet::new();
        let mut memo = std::collections::HashMap::new();
        return decide_inner(ctx, goal, &mut visiting, &mut memo);
    }
    let mut visiting = std::collections::HashSet::new();
    let mut memo = std::collections::HashMap::new();
    decide_fol_inner(ctx, goal, 0, 20, &mut visiting, &mut memo)
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
        Ty::Pred { sym, .. } => {
            out.insert(*sym);
        }
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => {
            collect_atoms(a, out);
            collect_atoms(b, out);
        }
        Ty::Forall(body) | Ty::Exists(body) => {
            collect_atoms(body, out);
        }
        Ty::Eq(_, _) | Ty::Bot => {}
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
        Ty::Pred { .. } | Ty::Forall(_) | Ty::Exists(_) | Ty::Eq(_, _) => false,
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
    if !is_propositional(goal) || ctx.iter().any(|t| !is_propositional(t)) {
        return None;
    }
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
