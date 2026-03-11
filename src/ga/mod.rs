pub mod corpus;

use crate::kernel::{Ctx, Tm, Ty, check, is_intuitionistic_theorem, normalize, tm_size};
use crate::search::{
    ChoiceStream, GoalStrategy, PTm, SearchConfig, SearchMetrics, SearchPolicy, beam_search,
    pretty_ptm, pretty_tm,
};
use rayon::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;

#[derive(Clone, Debug)]
pub struct Gene {
    pub data: Vec<u32>,
}

const TG_MAGIC: [u8; 4] = *b"TSDE";
const TG_VERSION: u8 = 1;

pub fn save_gene_tg<P: AsRef<Path>>(path: P, gene: &Gene) -> io::Result<()> {
    let mut f = File::create(path)?;
    f.write_all(&TG_MAGIC)?;
    f.write_all(&[TG_VERSION])?;
    let len = u32::try_from(gene.data.len())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "gene too long"))?;
    f.write_all(&len.to_le_bytes())?;
    for w in &gene.data {
        f.write_all(&w.to_le_bytes())?;
    }
    Ok(())
}

pub fn load_gene_tg<P: AsRef<Path>>(path: P) -> io::Result<Gene> {
    let mut f = File::open(path)?;
    let mut bytes = Vec::new();
    f.read_to_end(&mut bytes)?;

    if bytes.len() < 9 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid .tg: too short",
        ));
    }
    if bytes[0..4] != TG_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid .tg: bad magic",
        ));
    }
    if bytes[4] != TG_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid .tg: unsupported version",
        ));
    }

    let len = u32::from_le_bytes([bytes[5], bytes[6], bytes[7], bytes[8]]) as usize;
    let expected = 9usize.saturating_add(len.saturating_mul(4));
    if bytes.len() != expected {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid .tg: length mismatch",
        ));
    }

    let mut data = Vec::with_capacity(len);
    let mut off = 9usize;
    for _ in 0..len {
        let w = u32::from_le_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]]);
        data.push(w);
        off += 4;
    }
    Ok(Gene { data })
}

const POLICY_WORDS: usize = 12;

#[derive(Clone, Debug)]
pub struct GeneCursor {
    data: Vec<u32>,
    pc: usize,
}

impl GeneCursor {
    pub fn new(gene: &Gene) -> Self {
        let data = if gene.data.len() > POLICY_WORDS {
            gene.data[POLICY_WORDS..].to_vec()
        } else {
            Vec::new()
        };
        Self { data, pc: 0 }
    }
}

impl ChoiceStream for GeneCursor {
    fn next_u32(&mut self) -> u32 {
        if self.data.is_empty() {
            return 0;
        }
        let v = self.data[self.pc % self.data.len()];
        self.pc += 1;
        v
    }
}

#[derive(Clone, Debug)]
pub struct GenePolicy {
    pub search_policy: SearchPolicy,
    pub beam_bonus: usize,
    pub expand_bonus: usize,
    pub budget_bonus: u32,
}

impl GenePolicy {
    pub fn from_gene(gene: &Gene) -> Self {
        let g = |i: usize| -> u32 { gene.data.get(i).copied().unwrap_or(0) };
        let strategy = match g(5) % 3 {
            0 => GoalStrategy::Shallow,
            1 => GoalStrategy::Deep,
            _ => GoalStrategy::Random,
        };

        Self {
            search_policy: SearchPolicy {
                w_var: 1 + g(0) % 16,
                w_app: 1 + g(1) % 16,
                w_direct_app: 1 + g(1) % 16,
                w_hole: 1 + g(2) % 16,
                w_pair: 1 + g(3) % 16,
                w_proj: 1 + g(4) % 16,
                w_sum_intro: 1 + g(9) % 16,
                w_case: 1 + g(10) % 16,
                w_absurd: 1 + g(11) % 16,
                branch_budget_scale_per_mille: 500 + (g(8) % 501),
                goal_strategy: strategy,
            },
            beam_bonus: (g(6) % 8) as usize,
            expand_bonus: (g(7) % 5) as usize,
            budget_bonus: g(8) % 8,
        }
    }

    pub fn tune_search(&self, base: &SearchConfig) -> SearchConfig {
        let beam_width = (base.beam_width + self.beam_bonus).min(32);
        let expand_per_state = (base.expand_per_state + self.expand_bonus).min(6);
        let synth_budget = (base.synth_budget + self.budget_bonus).min(14);
        SearchConfig {
            beam_width,
            max_iters: base.max_iters,
            expand_per_state,
            synth_budget,
        }
    }
}

#[derive(Clone, Debug)]
pub struct GAConfig {
    pub population: usize,
    pub gene_len: usize,
    pub generations: usize,
    pub tournament_k: usize,
    pub crossover_rate: f64,
    pub mutation_rate: f64,
    pub search: SearchConfig,
}

impl Default for GAConfig {
    fn default() -> Self {
        Self {
            population: 200,
            gene_len: 256,
            generations: 500,
            tournament_k: 5,
            crossover_rate: 0.7,
            mutation_rate: 0.02,
            search: SearchConfig {
                beam_width: 20,
                max_iters: 120,
                expand_per_state: 3,
                synth_budget: 8,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct EvalResult {
    pub fitness: i64,
    pub term: Option<Tm>,
    pub search_metrics: SearchMetrics,
    pub best_partial_pretty: String,
    pub remaining_goals: Vec<(Ty, usize)>,
    pub remaining_goal_debug: Vec<RemainingGoalDebug>,
}

#[derive(Clone, Debug)]
pub struct RemainingGoalDebug {
    pub goal_id: u32,
    pub ty: Ty,
    pub ctx: Ctx,
    pub matching_vars: Vec<u32>,
    pub top_var_matches: bool,
    pub hole_path: String,
    pub hole_branch: String,
}

#[derive(Clone, Debug)]
pub struct GARunResult {
    pub best_gene: Gene,
    pub best_fitness: i64,
    pub best_term: Option<Tm>,
    pub best_term_pretty: Option<String>,
    pub best_partial_pretty: String,
    pub best_remaining_goals: Vec<(Ty, usize)>,
    pub best_remaining_goal_debug: Vec<RemainingGoalDebug>,
    pub best_metrics: SearchMetrics,
}

#[derive(Clone, Debug)]
struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    fn new(seed: u64) -> Self {
        let state = if seed == 0 { 0x9E3779B97F4A7C15 } else { seed };
        Self { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.state = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() & 0xFFFF_FFFF) as u32
    }

    fn gen_bool(&mut self, p: f64) -> bool {
        let p = p.clamp(0.0, 1.0);
        let threshold = (p * (u64::MAX as f64)) as u64;
        self.next_u64() <= threshold
    }

    fn gen_range_usize(&mut self, range: std::ops::Range<usize>) -> usize {
        let len = range.end - range.start;
        if len == 0 {
            return range.start;
        }
        range.start + (self.next_u64() as usize % len)
    }

    fn gen_range_u32(&mut self, range: std::ops::Range<u32>) -> u32 {
        let len = range.end - range.start;
        if len == 0 {
            return range.start;
        }
        range.start + (self.next_u32() % len)
    }
}

pub fn evaluate_gene(ctx: &Ctx, target: &Ty, gene: &Gene, cfg: &GAConfig) -> EvalResult {
    // 早期打ち切り: 時間のかかる探索の前に定理が証明可能か確認する
    if !is_intuitionistic_theorem(ctx, target) {
        // 証明不可能な定理に対しては低い適合度を返すことで進化を誘導する
        return EvalResult {
            fitness: -1_000_000,
            term: None,
            search_metrics: SearchMetrics {
                iterations: 0,
                expanded_states: 0,
                min_holes: 1,
                min_goal_complexity: crate::kernel::ty_size(target),
                min_root_size: 1,
                min_app_nodes: 0,
                min_case_nodes: 0,
                min_repeat_case_nodes: 0,
                max_pair_nodes_seen: 0,
                max_sum_intro_nodes_seen: 0,
                max_proj_nodes_seen: 0,
                dedup_dropped: 0,
                memo_hits: 0,
                repair_invocations: 0,
                repair_goal_attempts: 0,
                repair_candidates_tried: 0,
                repair_success_steps: 0,
                repair_promoted_states: 0,
            },
            best_partial_pretty: "unprovable".to_string(),
            remaining_goals: vec![(target.clone(), 1)],
            remaining_goal_debug: vec![],
        };
    }

    let policy = GenePolicy::from_gene(gene);
    let tuned_search = policy.tune_search(&cfg.search);
    let mut cursor = GeneCursor::new(gene);
    let out = beam_search(
        ctx,
        target,
        &mut cursor,
        &tuned_search,
        &policy.search_policy,
    );
    let best_partial_pretty = pretty_ptm(&out.best_state.root);
    let mut rem: HashMap<Ty, usize> = HashMap::new();
    for g in out.best_state.goals.values() {
        *rem.entry(g.ty.clone()).or_insert(0) += 1;
    }
    let mut remaining_goals: Vec<(Ty, usize)> = rem.into_iter().collect();
    remaining_goals.sort_by_key(|(ty, n)| (crate::kernel::ty_size(ty), *n));
    let mut remaining_goal_debug = Vec::new();
    for g in out.best_state.goals.values() {
        let mut matching_vars = Vec::new();
        for i in 0..g.ctx.len() {
            let db = i as u32;
            let cty = &g.ctx[g.ctx.len() - 1 - i];
            if *cty == g.ty {
                matching_vars.push(db);
            }
        }
        remaining_goal_debug.push(RemainingGoalDebug {
            goal_id: g.id,
            ty: g.ty.clone(),
            ctx: g.ctx.clone(),
            top_var_matches: !g.ctx.is_empty() && g.ctx[g.ctx.len() - 1] == g.ty,
            matching_vars,
            hole_path: find_hole_path(&out.best_state.root, g.id)
                .unwrap_or_else(|| "<not-found>".to_string()),
            hole_branch: find_hole_branch(&out.best_state.root, g.id),
        });
    }
    remaining_goal_debug.sort_by_key(|d| (crate::kernel::ty_size(&d.ty), d.ctx.len()));

    if let Some(tm) = out.complete_term
        && check(ctx, &tm, target).is_ok()
    {
        let nf = normalize(&tm);
        let fitness = 2_000_000i64 + out.best_score
            - (tm_size(&tm) as i64) * 12
            - (tm_size(&nf) as i64) * 5
            - (out.metrics.iterations as i64) * 2;
        return EvalResult {
            fitness,
            term: Some(tm),
            search_metrics: out.metrics,
            best_partial_pretty,
            remaining_goals,
            remaining_goal_debug,
        };
    }

    // 失敗個体でも地形を滑らかにするため最良途中状態の統計を強く使う
    let m = &out.metrics;
    let smooth_penalty = (m.min_holes as i64) * 1500
        + (m.min_goal_complexity as i64) * 45
        + (m.min_root_size as i64) * 3
        + (m.min_app_nodes as i64) * 10
        + (m.min_case_nodes as i64) * 6
        + (m.min_repeat_case_nodes as i64) * 20
        + (m.iterations as i64);
    let fitness = out.best_score - smooth_penalty;

    EvalResult {
        fitness,
        term: None,
        search_metrics: out.metrics,
        best_partial_pretty,
        remaining_goals,
        remaining_goal_debug,
    }
}

fn find_hole_path(root: &PTm, hole_id: u32) -> Option<String> {
    fn go(tm: &PTm, hole_id: u32, path: &mut Vec<&'static str>) -> bool {
        match tm {
            PTm::Hole { id, .. } => *id == hole_id,
            PTm::Lam { body, .. } => {
                path.push("Lam");
                let ok = go(body, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::App(f, x) => {
                path.push("AppF");
                if go(f, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("AppX");
                let ok = go(x, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Pair(a, b) => {
                path.push("PairL");
                if go(a, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("PairR");
                let ok = go(b, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Inl { term, .. } => {
                path.push("Inl");
                let ok = go(term, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Inr { term, .. } => {
                path.push("Inr");
                let ok = go(term, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Case { scrut, left, right } => {
                path.push("CaseS");
                if go(scrut, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("CaseL");
                if go(left, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("CaseR");
                let ok = go(right, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Fst(t) => {
                path.push("Fst");
                let ok = go(t, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Snd(t) => {
                path.push("Snd");
                let ok = go(t, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Absurd { bot_term, .. } => {
                path.push("Absurd");
                let ok = go(bot_term, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::TLam { body } => {
                path.push("TLam");
                let ok = go(body, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::TApp { term, .. } => {
                path.push("TApp");
                let ok = go(term, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Pack { body, .. } => {
                path.push("Pack");
                let ok = go(body, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Unpack { scrut, body } => {
                path.push("UnpackS");
                if go(scrut, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("UnpackB");
                let ok = go(body, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Refl { .. } => false,
            PTm::Subst { eq_proof, body, .. } => {
                path.push("SubstEq");
                if go(eq_proof, hole_id, path) {
                    return true;
                }
                path.pop();
                path.push("SubstB");
                let ok = go(body, hole_id, path);
                if !ok {
                    path.pop();
                }
                ok
            }
            PTm::Var(_) => false,
        }
    }

    let mut path = Vec::new();
    if go(root, hole_id, &mut path) {
        Some(path.join("/"))
    } else {
        None
    }
}

fn find_hole_branch(root: &PTm, hole_id: u32) -> String {
    let Some(path) = find_hole_path(root, hole_id) else {
        return "outside-case".to_string();
    };
    let segs: Vec<&str> = path.split('/').collect();
    for seg in segs.iter().rev() {
        if *seg == "CaseL" {
            return "left-branch".to_string();
        }
        if *seg == "CaseR" {
            return "right-branch".to_string();
        }
    }
    "outside-case".to_string()
}

fn random_gene(rng: &mut SimpleRng, len: usize) -> Gene {
    let data = (0..len).map(|_| rng.next_u32()).collect();
    Gene { data }
}

fn tournament_select<'a>(
    pool: &'a [(Gene, EvalResult)],
    k: usize,
    rng: &mut SimpleRng,
) -> &'a (Gene, EvalResult) {
    let mut best: Option<&(Gene, EvalResult)> = None;
    let rounds = k.max(1);
    for _ in 0..rounds {
        let cand = &pool[rng.gen_range_usize(0..pool.len())];
        match best {
            Some(b) if b.1.fitness >= cand.1.fitness => {}
            _ => best = Some(cand),
        }
    }
    best.expect("tournament_select requires non-empty pool")
}

fn crossover(a: &Gene, b: &Gene, rng: &mut SimpleRng) -> Gene {
    let len = a.data.len().min(b.data.len());
    if len == 0 {
        return Gene { data: Vec::new() };
    }
    let p = rng.gen_range_usize(0..len);
    let mut out = Vec::with_capacity(len);
    out.extend_from_slice(&a.data[..p]);
    out.extend_from_slice(&b.data[p..len]);
    Gene { data: out }
}

fn mutate(gene: &mut Gene, rate: f64, rng: &mut SimpleRng) {
    if gene.data.is_empty() {
        return;
    }
    for x in &mut gene.data {
        if rng.gen_bool(rate.clamp(0.0, 1.0)) {
            match rng.gen_range_u32(0..3) {
                0 => *x = rng.next_u32(),
                1 => *x ^= 1 << rng.gen_range_u32(0..31),
                _ => *x = x.rotate_left(rng.gen_range_u32(1..32)),
            }
        }
    }
}

pub fn evolve_theorem(ctx: &Ctx, target: &Ty, cfg: &GAConfig, seed: u64) -> GARunResult {
    let mut rng = SimpleRng::new(seed);
    let mut population: Vec<Gene> = (0..cfg.population)
        .map(|_| random_gene(&mut rng, cfg.gene_len))
        .collect();

    let mut best_gene = Gene { data: Vec::new() };
    let mut best_eval = EvalResult {
        fitness: i64::MIN,
        term: None,
        search_metrics: SearchMetrics::default(),
        best_partial_pretty: String::new(),
        remaining_goals: Vec::new(),
        remaining_goal_debug: Vec::new(),
    };

    for _gen in 0..cfg.generations {
        // 個体群の並列評価
        let evaluated: Vec<(Gene, EvalResult)> = population
            .into_par_iter()
            .map(|g| {
                let eval = evaluate_gene(ctx, target, &g, cfg);
                (g, eval)
            })
            .collect();

        for (g, e) in &evaluated {
            if e.fitness > best_eval.fitness {
                best_gene = g.clone();
                best_eval = e.clone();
            }
        }

        if best_eval.term.is_some() {
            break;
        }

        let mut next_pop = Vec::with_capacity(cfg.population);
        while next_pop.len() < cfg.population {
            let p1 = tournament_select(&evaluated, cfg.tournament_k, &mut rng)
                .0
                .clone();
            let p2 = tournament_select(&evaluated, cfg.tournament_k, &mut rng)
                .0
                .clone();

            let mut child = if rng.gen_bool(cfg.crossover_rate.clamp(0.0, 1.0)) {
                crossover(&p1, &p2, &mut rng)
            } else {
                p1
            };
            mutate(&mut child, cfg.mutation_rate, &mut rng);

            if child.data.len() != cfg.gene_len {
                child.data.resize(cfg.gene_len, 0);
            }
            next_pop.push(child);
        }
        population = next_pop;
    }

    let best_term_pretty = best_eval.term.as_ref().map(pretty_tm);
    GARunResult {
        best_gene,
        best_fitness: best_eval.fitness,
        best_term: best_eval.term,
        best_term_pretty,
        best_partial_pretty: best_eval.best_partial_pretty,
        best_remaining_goals: best_eval.remaining_goals,
        best_remaining_goal_debug: best_eval.remaining_goal_debug,
        best_metrics: best_eval.search_metrics,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn evolve_finds_identity_quickly() {
        let a = Ty::Atom(0);
        let target = Ty::Arr(Box::new(a.clone()), Box::new(a));
        let cfg = GAConfig {
            population: 20,
            gene_len: 24,
            generations: 50,
            tournament_k: 3,
            crossover_rate: 0.7,
            mutation_rate: 0.03,
            search: SearchConfig {
                beam_width: 10,
                max_iters: 40,
                expand_per_state: 2,
                synth_budget: 7,
            },
        };
        let out = evolve_theorem(&Vec::new(), &target, &cfg, 7);
        assert!(out.best_fitness > 0);
        assert!(out.best_term.is_some());
    }

    #[test]
    fn seed_is_reproducible() {
        let a = Ty::Atom(0);
        let target = Ty::Arr(Box::new(a.clone()), Box::new(a));
        let cfg = GAConfig {
            population: 16,
            gene_len: 20,
            generations: 20,
            tournament_k: 3,
            crossover_rate: 0.7,
            mutation_rate: 0.03,
            search: SearchConfig {
                beam_width: 8,
                max_iters: 24,
                expand_per_state: 2,
                synth_budget: 6,
            },
        };

        let r1 = evolve_theorem(&Vec::new(), &target, &cfg, 99);
        let r2 = evolve_theorem(&Vec::new(), &target, &cfg, 99);
        assert_eq!(r1.best_fitness, r2.best_fitness);
        assert_eq!(r1.best_term, r2.best_term);
        assert_eq!(r1.best_term_pretty, r2.best_term_pretty);
    }

    #[test]
    fn tg_roundtrip() {
        let gene = Gene {
            data: vec![1, 7, 42, u32::MAX],
        };
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time ok")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("tsade-{nonce}.tg"));

        save_gene_tg(&path, &gene).expect("save");
        let loaded = load_gene_tg(&path).expect("load");
        std::fs::remove_file(&path).ok();

        assert_eq!(gene.data, loaded.data);
    }

    #[test]
    fn tg_rejects_bad_magic() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time ok")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("tsade-bad-{nonce}.tg"));
        std::fs::write(&path, [0u8; 9]).expect("write");

        let err = load_gene_tg(&path).expect_err("must fail");
        std::fs::remove_file(&path).ok();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }
}
