use std::env;
use tsade_engine::ga::corpus::implication_corpus;
use tsade_engine::ga::{GAConfig, evaluate_gene, evolve_theorem, load_gene_tg, save_gene_tg};
use tsade_engine::kernel::normalize;
use tsade_engine::search::{pretty_tm, pretty_tm_unicode, pretty_ty, pretty_ty_unicode};

fn parse_opt_string(args: &[String], name: &str) -> Option<String> {
    args.windows(2).find_map(|w| {
        if w[0] == name {
            Some(w[1].clone())
        } else {
            None
        }
    })
}

fn parse_flag(args: &[String], name: &str) -> bool {
    args.iter().any(|arg| arg == name)
}

fn run_single(args: &[String]) {
    let theorem_name = parse_opt_string(args, "--theorem");
    let load_model = parse_opt_string(args, "--load");
    let save_model = parse_opt_string(args, "--save");
    let use_unicode = parse_flag(args, "--unicode");

    let Some(theorem_name) = theorem_name else {
        eprintln!("Error: --theorem <name> is required");
        eprintln!();
        eprintln!("Usage: tsade-engine single --theorem <name> [options]");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --theorem <name>  Theorem to prove (required)");
        eprintln!("  --unicode         Use Unicode symbols in output");
        eprintln!("  --save <file>     Save trained model to file");
        eprintln!("  --load <file>     Load model from file");
        eprintln!();
        eprintln!("Available theorems (first 20):");
        for c in implication_corpus().iter().take(20) {
            eprintln!("  {}", c.name);
        }
        std::process::exit(1);
    };

    let corpus = implication_corpus();
    let case = corpus.iter().find(|c| c.name == theorem_name);

    let Some(case) = case else {
        eprintln!("Error: Unknown theorem '{}'", theorem_name);
        eprintln!();
        eprintln!("Available theorems (first 20):");
        for c in corpus.iter().take(20) {
            eprintln!("  {}", c.name);
        }
        std::process::exit(1);
    };

    let cfg = GAConfig::default();
    let seed = 42;

    let (mode_name, best_gene, best_fitness, best_term) = if let Some(path) = &load_model {
        let gene = match load_gene_tg(path) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Error: Failed to load model from '{}': {}", path, e);
                std::process::exit(1);
            }
        };
        let eval = evaluate_gene(&case.ctx, &case.target, &gene, &cfg);
        ("load", gene, eval.fitness, eval.term)
    } else {
        let out = evolve_theorem(&case.ctx, &case.target, &cfg, seed);
        ("evolve", out.best_gene, out.best_fitness, out.best_term)
    };

    if let Some(path) = &save_model {
        if let Err(e) = save_gene_tg(path, &best_gene) {
            eprintln!("Error: Failed to save model to '{}': {}", path, e);
            std::process::exit(1);
        }
        println!("Model saved to: {}", path);
    }

    println!("Theorem: {}", case.name);
    if use_unicode {
        println!("Goal:    {}", pretty_ty_unicode(&case.target));
    } else {
        println!("Goal:    {}", pretty_ty(&case.target));
    }
    println!("Mode:    {}", mode_name);
    println!("Fitness: {}", best_fitness);

    match best_term {
        Some(tm) => {
            let nf = normalize(&tm);
            println!("Status:  ✓ Proved");
            if use_unicode {
                println!("Proof:   {}", pretty_tm_unicode(&tm));
                println!("Normal:  {}", pretty_tm_unicode(&nf));
            } else {
                println!("Proof:   {}", pretty_tm(&tm));
                println!("Normal:  {}", pretty_tm(&nf));
            }
        }
        None => {
            println!("Status:  ✗ Not found");
        }
    }
}

fn run_all_corpus(args: &[String]) {
    let use_unicode = parse_flag(args, "--unicode");
    let corpus = implication_corpus();
    let cfg = GAConfig::default();
    let seed: u64 = 42;

    println!(
        "Running all {} theorems from implication_corpus...",
        corpus.len()
    );

    let mut total = 0;
    let mut proved = 0;
    let mut expected_provable = 0;
    let mut tp = 0; // True Positive
    let mut tn = 0; // True Negative
    let mut fp = 0; // False Positive
    let mut fn_count = 0; // False Negative

    for (idx, case) in corpus.iter().enumerate() {
        println!();

        total += 1;
        if case.expected_provable {
            expected_provable += 1;
        }

        let out = evolve_theorem(&case.ctx, &case.target, &cfg, seed.wrapping_add(idx as u64));
        let solved = out.best_term.is_some();

        if solved {
            proved += 1;
        }

        let status = match (case.expected_provable, solved) {
            (true, true) => {
                tp += 1;
                "✓"
            }
            (false, false) => {
                tn += 1;
                "✓"
            }
            (false, true) => {
                fp += 1;
                "✗ FP"
            }
            (true, false) => {
                fn_count += 1;
                "✗ FN"
            }
        };

        print!(" {:02}. {} {:<30}", idx + 1, status, case.name);
        if use_unicode {
            print!(" {}", pretty_ty_unicode(&case.target));
        } else {
            print!(" {}", pretty_ty(&case.target));
        }
        println!();

        if solved && use_unicode {
            if let Some(tm) = &out.best_term {
                println!(" {}", pretty_tm_unicode(tm));
            }
        } else if solved && let Some(tm) = &out.best_term {
            println!(" {}", pretty_tm(tm));
        }
    }

    println!();
    println!("===========================");
    println!(" Summary");
    println!("===========================");
    println!("Total theorems:       {}", total);
    println!("Expected provable:    {}", expected_provable);
    println!("Actually proved:      {}", proved);
    println!(
        "Success rate:         {:.1}%",
        100.0 * proved as f64 / total as f64
    );
    println!();
    println!("True Positive (TP):   {} (provable & proved)", tp);
    println!("True Negative (TN):   {} (unprovable & not proved)", tn);
    println!("False Positive (FP):  {} (unprovable but proved)", fp);
    println!(
        "False Negative (FN):  {} (provable but not proved)",
        fn_count
    );
    println!();
    if fp == 0 && fn_count == 0 {
        println!("✓ All theorems correctly classified!");
    } else {
        println!("✗ Some theorems misclassified");
    }
}

fn print_usage() {
    eprintln!("TsadeEngine - Theorem Proving with Genetic Algorithm");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  tsade-engine single --theorem <name> [options]");
    eprintln!("  tsade-engine all-corpus [options]");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  single       Prove a single theorem");
    eprintln!("  all-corpus   Run all theorems from the corpus");
    eprintln!();
    eprintln!("Options for 'single':");
    eprintln!("  --theorem <name>  Theorem to prove (required)");
    eprintln!("  --unicode         Use Unicode symbols in output");
    eprintln!("  --save <file>     Save trained model to file");
    eprintln!("  --load <file>     Load model from file");
    eprintln!();
    eprintln!("Options for 'all-corpus':");
    eprintln!("  --unicode         Use Unicode symbols in output");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  tsade-engine single --theorem Curry --unicode");
    eprintln!("  tsade-engine single --theorem Flip --save flip.tg");
    eprintln!("  tsade-engine single --theorem Uncurry --load flip.tg");
    eprintln!("  tsade-engine all-corpus --unicode");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }

    let command = &args[1];
    match command.as_str() {
        "single" => run_single(&args),
        "all-corpus" => run_all_corpus(&args),
        "--help" | "-h" => {
            print_usage();
        }
        _ => {
            eprintln!("Error: Unknown command '{}'", command);
            eprintln!();
            print_usage();
            std::process::exit(1);
        }
    }
}
