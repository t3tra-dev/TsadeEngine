use crate::ga::corpus::{TheoremCase, TheoremCaseCategory};
use crate::kernel::{Tm, normalize_eta};
use crate::search::{
    ChoiceStream, PartialFeatures, SearchConfig, SearchOutcome, SearchPolicy, beam_search,
    partial_features,
};

#[derive(Clone, Debug)]
pub struct ProbeConfig {
    pub search: SearchConfig,
    pub policy: SearchPolicy,
}

impl Default for ProbeConfig {
    fn default() -> Self {
        Self {
            search: SearchConfig {
                beam_width: 6,
                max_iters: 20,
                expand_per_state: 6,
                synth_budget: 4,
            },
            policy: SearchPolicy::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProbeStatus {
    TruePositive,
    TrueNegative,
    FalsePositive,
    FalseNegative,
}

impl ProbeStatus {
    pub fn label(self) -> &'static str {
        match self {
            Self::TruePositive => "✓TP   ",
            Self::TrueNegative => "✓TN   ",
            Self::FalsePositive => "FP    ",
            Self::FalseNegative => "FN    ",
        }
    }

    pub fn flag(self) -> &'static str {
        match self {
            Self::TruePositive | Self::TrueNegative => "",
            Self::FalsePositive => " !!",
            Self::FalseNegative => " !",
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ProbeTotals {
    pub tp: usize,
    pub tn: usize,
    pub fp: usize,
    pub fn_: usize,
}

impl ProbeTotals {
    fn record(&mut self, status: ProbeStatus) {
        match status {
            ProbeStatus::TruePositive => self.tp += 1,
            ProbeStatus::TrueNegative => self.tn += 1,
            ProbeStatus::FalsePositive => self.fp += 1,
            ProbeStatus::FalseNegative => self.fn_ += 1,
        }
    }

    pub fn all_correct(&self) -> bool {
        self.fp == 0 && self.fn_ == 0
    }
}

#[derive(Clone, Debug)]
pub struct ProbeCaseReport {
    pub category_name: &'static str,
    pub case_index: usize,
    pub case: TheoremCase,
    pub outcome: SearchOutcome,
    pub features: PartialFeatures,
    pub status: ProbeStatus,
    pub normalized_term: Option<Tm>,
}

impl ProbeCaseReport {
    pub fn solved(&self) -> bool {
        self.outcome.complete_term.is_some()
    }
}

#[derive(Clone, Debug)]
pub struct ProbeCategoryReport {
    pub category_name: &'static str,
    pub cases: Vec<ProbeCaseReport>,
    pub totals: ProbeTotals,
}

impl ProbeCategoryReport {
    pub fn all_correct(&self) -> bool {
        self.totals.all_correct()
    }
}

#[derive(Clone, Debug)]
pub struct ProbeRunReport {
    pub categories: Vec<ProbeCategoryReport>,
    pub totals: ProbeTotals,
}

impl ProbeRunReport {
    pub fn all_correct(&self) -> bool {
        self.totals.all_correct()
    }
}

#[derive(Clone, Debug)]
struct ProbeRng(u64);

impl ChoiceStream for ProbeRng {
    fn next_u32(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        (x >> 32) as u32
    }
}

fn classify(expected_provable: bool, solved: bool) -> ProbeStatus {
    match (expected_provable, solved) {
        (true, true) => ProbeStatus::TruePositive,
        (false, false) => ProbeStatus::TrueNegative,
        (false, true) => ProbeStatus::FalsePositive,
        (true, false) => ProbeStatus::FalseNegative,
    }
}

pub fn run_category_probe(
    category: &TheoremCaseCategory,
    cfg: &ProbeConfig,
) -> ProbeCategoryReport {
    let mut totals = ProbeTotals::default();
    let mut cases = Vec::with_capacity(category.cases.len());

    for (idx, case) in category.cases.iter().enumerate() {
        let seed = 0x9E37_79B9_u64
            .wrapping_add(idx as u64)
            .wrapping_mul(6364136223846793005)
            | 1;
        let mut rng = ProbeRng(seed);
        let outcome = beam_search(&case.ctx, &case.target, &mut rng, &cfg.search, &cfg.policy);
        let features = partial_features(&outcome.best_state);
        let normalized_term = outcome.complete_term.as_ref().map(normalize_eta);
        let status = classify(case.expected_provable, outcome.complete_term.is_some());
        totals.record(status);
        cases.push(ProbeCaseReport {
            category_name: category.name,
            case_index: idx,
            case: case.clone(),
            outcome,
            features,
            status,
            normalized_term,
        });
    }

    ProbeCategoryReport {
        category_name: category.name,
        cases,
        totals,
    }
}

pub fn run_probe(categories: &[TheoremCaseCategory], cfg: &ProbeConfig) -> ProbeRunReport {
    let mut totals = ProbeTotals::default();
    let mut reports = Vec::with_capacity(categories.len());

    for category in categories {
        let report = run_category_probe(category, cfg);
        totals.tp += report.totals.tp;
        totals.tn += report.totals.tn;
        totals.fp += report.totals.fp;
        totals.fn_ += report.totals.fn_;
        reports.push(report);
    }

    ProbeRunReport {
        categories: reports,
        totals,
    }
}
