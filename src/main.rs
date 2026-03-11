use std::env;

use tsade_engine::ga::corpus::{
    TheoremCaseCategory, theorem_case_categories, theorem_case_category,
    theorem_case_category_names,
};
use tsade_engine::probe::{ProbeCategoryReport, ProbeConfig, ProbeRunReport, run_probe};
use tsade_engine::search::{
    pretty_ptm, pretty_ptm_unicode, pretty_tm, pretty_tm_unicode, pretty_ty, pretty_ty_unicode,
};

fn parse_opt_string(args: &[String], name: &str) -> Option<String> {
    args.windows(2).find_map(|w| {
        if w[0] == name {
            Some(w[1].clone())
        } else {
            None
        }
    })
}

fn parse_opt_usize(args: &[String], name: &str) -> Option<usize> {
    parse_opt_string(args, name).and_then(|s| s.parse::<usize>().ok())
}

fn parse_opt_u32(args: &[String], name: &str) -> Option<u32> {
    parse_opt_string(args, name).and_then(|s| s.parse::<u32>().ok())
}

fn parse_flag(args: &[String], name: &str) -> bool {
    args.iter().any(|arg| arg == name)
}

fn build_probe_config(args: &[String]) -> ProbeConfig {
    let mut cfg = ProbeConfig::default();
    if let Some(v) = parse_opt_usize(args, "--iters") {
        cfg.search.max_iters = v;
    }
    if let Some(v) = parse_opt_usize(args, "--beam-width") {
        cfg.search.beam_width = v.max(1);
    }
    if let Some(v) = parse_opt_usize(args, "--expand-per-state") {
        cfg.search.expand_per_state = v.max(1);
    }
    if let Some(v) = parse_opt_u32(args, "--synth-budget") {
        cfg.search.synth_budget = v;
    }
    cfg
}

fn resolve_categories(name: &str) -> Option<Vec<TheoremCaseCategory>> {
    if name == "all" {
        return Some(theorem_case_categories());
    }
    theorem_case_category(name).map(|cat| vec![cat])
}

fn print_available_categories() {
    eprintln!("Available categories:");
    eprintln!("  all");
    for name in theorem_case_category_names() {
        eprintln!("  {}", name);
    }
}

fn print_probe_case_details(report: &ProbeCategoryReport, case_idx: usize, use_unicode: bool) {
    let case = &report.cases[case_idx];
    println!();
    println!("  Category: {}", case.category_name);
    println!(
        "  Goal:    {}",
        if use_unicode {
            pretty_ty_unicode(&case.case.target)
        } else {
            pretty_ty(&case.case.target)
        }
    );

    println!(
        "  Partial: {}",
        if use_unicode {
            pretty_ptm_unicode(&case.outcome.best_state.root)
        } else {
            pretty_ptm(&case.outcome.best_state.root)
        }
    );

    if !case.outcome.best_state.goals.is_empty() {
        println!(
            "  Remaining goals ({}):",
            case.outcome.best_state.goals.len()
        );
        let mut goals: Vec<_> = case.outcome.best_state.goals.values().collect();
        goals.sort_by_key(|g| g.id);
        for g in goals {
            println!(
                "    hole#{}: {}",
                g.id,
                if use_unicode {
                    pretty_ty_unicode(&g.ty)
                } else {
                    pretty_ty(&g.ty)
                }
            );
        }
    }

    if let Some(norm) = &case.normalized_term {
        let norm_str = if use_unicode {
            pretty_tm_unicode(norm)
        } else {
            pretty_tm(norm)
        };
        println!("  Proved:  {}", norm_str);
        if let Some(raw) = &case.outcome.complete_term
            && raw != norm
        {
            let raw_str = if use_unicode {
                pretty_tm_unicode(raw)
            } else {
                pretty_tm(raw)
            };
            println!("  Raw:     {}", raw_str);
        }
    }

    let m = &case.outcome.metrics;
    let f = &case.features;
    println!(
        "  Metrics: iters={}  expanded={}  dedup_dropped={}  memo_hits={}  repair_promoted={}",
        m.iterations, m.expanded_states, m.dedup_dropped, m.memo_hits, m.repair_promoted_states
    );
    println!(
        "  Features: tlam={}  pack={}  fo_witness_cost={}  repeat_case={}",
        f.tlam_nodes, f.pack_nodes, f.fo_witness_cost, f.repeat_case_nodes
    );
    println!();
}

fn print_category_report(
    report: &ProbeCategoryReport,
    use_unicode: bool,
    verbose_case: Option<&str>,
) -> bool {
    println!("=== Category: {} ===", report.category_name);
    println!(
        "{:<24} {:>3}  {:<6}  {:>8}  {:>5}  {:>5}  {:>5}  {:>5}  {:>6}  {:>5}",
        "name", "exp", "status", "score", "holes", "gc", "tlam", "pack", "fowit", "iters"
    );
    println!("{}", "-".repeat(85));

    let mut verbose_matched = false;

    for (idx, case) in report.cases.iter().enumerate() {
        println!(
            "{:<24} {:>3}  {}  {:>8}  {:>5}  {:>5}  {:>5}  {:>5}  {:>6}  {:>5}{}",
            case.case.name,
            if case.case.expected_provable {
                "P"
            } else {
                "U"
            },
            case.status.label(),
            case.outcome.best_score,
            case.features.holes,
            case.features.goal_complexity,
            case.features.tlam_nodes,
            case.features.pack_nodes,
            case.features.fo_witness_cost,
            case.outcome.metrics.iterations,
            case.status.flag()
        );

        if verbose_case == Some(case.case.name.as_str()) {
            verbose_matched = true;
            print_probe_case_details(report, idx, use_unicode);
        }
    }

    println!("{}", "-".repeat(85));
    println!(
        "TP={}  TN={}  FP={}  FN={}",
        report.totals.tp, report.totals.tn, report.totals.fp, report.totals.fn_
    );
    if report.all_correct() {
        println!("All correctly classified.");
    }
    println!();

    verbose_matched
}

fn print_run_report(
    run: &ProbeRunReport,
    cfg: &ProbeConfig,
    use_unicode: bool,
    verbose_case: Option<&str>,
) {
    println!("=== Probe ===");
    println!(
        "Config: beam_width={}  max_iters={}  expand_per_state={}  synth_budget={}",
        cfg.search.beam_width,
        cfg.search.max_iters,
        cfg.search.expand_per_state,
        cfg.search.synth_budget
    );
    println!();

    let mut verbose_matched = verbose_case.is_none();
    for report in &run.categories {
        verbose_matched |= print_category_report(report, use_unicode, verbose_case);
    }

    if run.categories.len() > 1 {
        println!("=== Overall ===");
        println!(
            "TP={}  TN={}  FP={}  FN={}",
            run.totals.tp, run.totals.tn, run.totals.fp, run.totals.fn_
        );
        if run.all_correct() {
            println!("All correctly classified.");
        }
    }

    if let Some(case_name) = verbose_case
        && !verbose_matched
    {
        eprintln!(
            "Warning: case '{}' was not found in the selected categories.",
            case_name
        );
    }
}

fn print_usage() {
    eprintln!("TsadeEngine - Unified theorem probe");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  tsade-engine probe --category <name> [options]");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  probe       Run the selected theorem category with beam-search probing");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --category <name>       Category to run (required, use 'all' for every category)");
    eprintln!("  --case <name>           Print detailed output for a specific theorem case");
    eprintln!("  --iters <n>             Max iterations per case");
    eprintln!("  --beam-width <n>        Beam width");
    eprintln!("  --expand-per-state <n>  Expansions per state");
    eprintln!("  --synth-budget <n>      Synthesis budget");
    eprintln!("  --unicode               Use Unicode symbols in output");
    eprintln!();
    print_available_categories();
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  tsade-engine probe --category arith --case C3_OnePlusOne");
    eprintln!("  tsade-engine probe --category implication --iters 30");
    eprintln!("  tsade-engine probe --category all --unicode");
}

fn run_probe_command(args: &[String]) {
    let Some(category_name) = parse_opt_string(args, "--category") else {
        eprintln!("Error: --category <name> is required");
        eprintln!();
        print_usage();
        std::process::exit(1);
    };

    let Some(categories) = resolve_categories(&category_name) else {
        eprintln!("Error: Unknown category '{}'", category_name);
        eprintln!();
        print_available_categories();
        std::process::exit(1);
    };

    let cfg = build_probe_config(args);
    let use_unicode = parse_flag(args, "--unicode");
    let verbose_case = parse_opt_string(args, "--case");
    let run = run_probe(&categories, &cfg);
    print_run_report(&run, &cfg, use_unicode, verbose_case.as_deref());
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }

    match args[1].as_str() {
        "probe" => run_probe_command(&args),
        "--help" | "-h" => print_usage(),
        other => {
            eprintln!("Error: Unknown command '{}'", other);
            eprintln!();
            print_usage();
            std::process::exit(1);
        }
    }
}
