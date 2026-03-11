use super::{PTm, SearchState};
use std::collections::HashMap;

/// DOT 形式で探索木を可視化するための構造体
/// 各ノードは探索状態を表しエッジは展開を表す
pub struct DotVisualizer {
    nodes: Vec<(usize, String, bool)>, // (id, label, is_complete)
    edges: Vec<(usize, usize)>,        // (from, to)
    next_id: usize,
}

impl Default for DotVisualizer {
    fn default() -> Self {
        Self::new()
    }
}

impl DotVisualizer {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            next_id: 0,
        }
    }

    /// 探索状態をノードとして追加
    pub fn add_state(&mut self, state: &SearchState, is_complete: bool) -> usize {
        let id = self.next_id;
        self.next_id += 1;

        let label = format!(
            "holes={} | size={}",
            state.goals.len(),
            ptm_node_count(&state.root)
        );

        self.nodes.push((id, label, is_complete));
        id
    }

    /// 探索状態の展開を表すエッジを追加
    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.edges.push((from, to));
    }

    /// DOT 形式の文字列を生成
    pub fn to_dot(&self) -> String {
        let mut dot = String::from("digraph SearchTree {\n");
        dot.push_str("  rankdir=TB;\n");
        dot.push_str("  node [shape=box, style=rounded];\n\n");

        // Add nodes
        for (id, label, is_complete) in &self.nodes {
            let color = if *is_complete {
                "lightgreen"
            } else {
                "lightblue"
            };
            dot.push_str(&format!(
                "  n{} [label=\"{}\", fillcolor={}, style=\"rounded,filled\"];\n",
                id, label, color
            ));
        }

        dot.push('\n');

        // Add edges
        for (from, to) in &self.edges {
            dot.push_str(&format!("  n{} -> n{};\n", from, to));
        }

        dot.push_str("}\n");
        dot
    }

    /// DOT をファイルに保存
    pub fn save(&self, path: &str) -> std::io::Result<()> {
        std::fs::write(path, self.to_dot())
    }
}

fn ptm_node_count(tm: &PTm) -> usize {
    match tm {
        PTm::Hole { .. } => 1,
        PTm::Var(_) => 1,
        PTm::Lam { body, .. } => 1 + ptm_node_count(body),
        PTm::App(f, x) => 1 + ptm_node_count(f) + ptm_node_count(x),
        PTm::Pair(a, b) => 1 + ptm_node_count(a) + ptm_node_count(b),
        PTm::Fst(t) | PTm::Snd(t) => 1 + ptm_node_count(t),
        PTm::Inl { term, .. } | PTm::Inr { term, .. } => 1 + ptm_node_count(term),
        PTm::Case { scrut, left, right } => {
            1 + ptm_node_count(scrut) + ptm_node_count(left) + ptm_node_count(right)
        }
        PTm::Absurd { bot_term, .. } => 1 + ptm_node_count(bot_term),
        PTm::TLam { body } => 1 + ptm_node_count(body),
        PTm::TApp { term, .. } => 1 + ptm_node_count(term),
        PTm::Pack { body, .. } => 1 + ptm_node_count(body),
        PTm::Unpack { scrut, body } => 1 + ptm_node_count(scrut) + ptm_node_count(body),
        PTm::Refl { .. } => 1,
        PTm::Subst { eq_proof, body, .. } => 1 + ptm_node_count(eq_proof) + ptm_node_count(body),
    }
}

/// 探索の進行状況を記録するためのトレース構造
pub struct SearchTrace {
    pub iterations: Vec<IterationTrace>,
}

pub struct IterationTrace {
    pub iteration: usize,
    pub beam: Vec<StateSnapshot>,
    pub expansions: Vec<(usize, usize)>, // (parent_idx, child_idx)
}

pub struct StateSnapshot {
    pub holes: usize,
    pub goal_complexity: usize,
    pub root_size: usize,
    pub score: i64,
    pub is_complete: bool,
}

impl Default for SearchTrace {
    fn default() -> Self {
        Self::new()
    }
}

impl SearchTrace {
    pub fn new() -> Self {
        Self {
            iterations: Vec::new(),
        }
    }

    pub fn add_iteration(&mut self, iter: IterationTrace) {
        self.iterations.push(iter);
    }

    /// DOT 形式で探索トレースを生成
    pub fn to_dot(&self) -> String {
        let mut dot = String::from("digraph SearchTrace {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=box, style=rounded];\n\n");

        let mut node_id = 0;
        let mut iter_node_map: Vec<HashMap<usize, usize>> = Vec::new();

        // 各イテレーションのノードを生成
        for iter in self.iterations.iter() {
            dot.push_str(&format!("  // Iteration {}\n", iter.iteration));

            let mut node_map = HashMap::new();
            for (state_idx, state) in iter.beam.iter().enumerate() {
                let color = if state.is_complete {
                    "lightgreen"
                } else {
                    "lightblue"
                };

                dot.push_str(&format!(
                    "  n{} [label=\"iter={} | h={} | gc={} | s={}\", fillcolor={}, style=\"rounded,filled\"];\n",
                    node_id, iter.iteration, state.holes, state.goal_complexity, state.score, color
                ));

                node_map.insert(state_idx, node_id);
                node_id += 1;
            }

            iter_node_map.push(node_map);
        }

        dot.push('\n');

        // 各イテレーション間のエッジを生成
        for (iter_idx, iter) in self.iterations.iter().enumerate() {
            if iter_idx == 0 {
                continue;
            }

            for (parent_idx, child_idx) in &iter.expansions {
                if let (Some(&parent_node), Some(&child_node)) = (
                    iter_node_map
                        .get(iter_idx - 1)
                        .and_then(|m| m.get(parent_idx)),
                    iter_node_map.get(iter_idx).and_then(|m| m.get(child_idx)),
                ) {
                    dot.push_str(&format!("  n{} -> n{};\n", parent_node, child_node));
                }
            }
        }

        dot.push_str("}\n");
        dot
    }

    pub fn save(&self, path: &str) -> std::io::Result<()> {
        std::fs::write(path, self.to_dot())
    }
}
