#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FOTerm {
    Var(u32),
    Const(u32),
    Func { sym: u32, args: Vec<FOTerm> },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FOFormula {
    Pred { sym: u32, args: Vec<FOTerm> },
    Bot,
    Arr(Box<FOFormula>, Box<FOFormula>),
    Prod(Box<FOFormula>, Box<FOFormula>),
    Sum(Box<FOFormula>, Box<FOFormula>),
    Forall(Box<FOFormula>),
    Exists(Box<FOFormula>),
}

pub fn term_shift(d: i32, cutoff: u32, tm: &FOTerm) -> FOTerm {
    match tm {
        FOTerm::Var(i) => {
            if *i >= cutoff {
                let next = ((*i as i64) + (d as i64)).max(0) as u32;
                FOTerm::Var(next)
            } else {
                FOTerm::Var(*i)
            }
        }
        FOTerm::Const(c) => FOTerm::Const(*c),
        FOTerm::Func { sym, args } => FOTerm::Func {
            sym: *sym,
            args: args.iter().map(|a| term_shift(d, cutoff, a)).collect(),
        },
    }
}

pub fn term_subst(j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
    fn walk(c: u32, j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
        match tm {
            FOTerm::Var(i) => {
                if *i == j + c {
                    term_shift(c as i32, 0, s)
                } else {
                    FOTerm::Var(*i)
                }
            }
            FOTerm::Const(k) => FOTerm::Const(*k),
            FOTerm::Func { sym, args } => FOTerm::Func {
                sym: *sym,
                args: args.iter().map(|a| walk(c, j, s, a)).collect(),
            },
        }
    }
    walk(0, j, s, tm)
}

pub fn term_subst_top(s: &FOTerm, body: &FOTerm) -> FOTerm {
    let su = term_shift(1, 0, s);
    let sub = term_subst(0, &su, body);
    term_shift(-1, 0, &sub)
}

pub fn formula_term_subst(j: u32, s: &FOTerm, fm: &FOFormula) -> FOFormula {
    fn walk(c: u32, j: u32, s: &FOTerm, fm: &FOFormula) -> FOFormula {
        match fm {
            FOFormula::Pred { sym, args } => FOFormula::Pred {
                sym: *sym,
                args: args
                    .iter()
                    .map(|a| {
                        let shifted = term_shift(c as i32, 0, a);
                        term_subst(j + c, s, &shifted)
                    })
                    .collect(),
            },
            FOFormula::Bot => FOFormula::Bot,
            FOFormula::Arr(a, b) => {
                FOFormula::Arr(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b)))
            }
            FOFormula::Prod(a, b) => {
                FOFormula::Prod(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b)))
            }
            FOFormula::Sum(a, b) => {
                FOFormula::Sum(Box::new(walk(c, j, s, a)), Box::new(walk(c, j, s, b)))
            }
            FOFormula::Forall(body) => FOFormula::Forall(Box::new(walk(c + 1, j, s, body))),
            FOFormula::Exists(body) => FOFormula::Exists(Box::new(walk(c + 1, j, s, body))),
        }
    }
    walk(0, j, s, fm)
}

pub fn formula_size(fm: &FOFormula) -> usize {
    match fm {
        FOFormula::Pred { args, .. } => 1 + args.iter().map(term_size).sum::<usize>(),
        FOFormula::Bot => 1,
        FOFormula::Arr(a, b) | FOFormula::Prod(a, b) | FOFormula::Sum(a, b) => {
            1 + formula_size(a) + formula_size(b)
        }
        FOFormula::Forall(x) | FOFormula::Exists(x) => 1 + formula_size(x),
    }
}

pub fn term_size(tm: &FOTerm) -> usize {
    match tm {
        FOTerm::Var(_) | FOTerm::Const(_) => 1,
        FOTerm::Func { args, .. } => 1 + args.iter().map(term_size).sum::<usize>(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_shift_basic() {
        assert_eq!(term_shift(1, 0, &FOTerm::Var(0)), FOTerm::Var(1));
        assert_eq!(term_shift(1, 1, &FOTerm::Var(0)), FOTerm::Var(0));
    }

    #[test]
    fn term_subst_top_basic() {
        let body = FOTerm::Var(0);
        let arg = FOTerm::Const(7);
        assert_eq!(term_subst_top(&arg, &body), FOTerm::Const(7));
    }

    #[test]
    fn formula_size_nonzero() {
        let f = FOFormula::Forall(Box::new(FOFormula::Arr(
            Box::new(FOFormula::Pred {
                sym: 0,
                args: vec![FOTerm::Var(0)],
            }),
            Box::new(FOFormula::Bot),
        )));
        assert!(formula_size(&f) >= 3);
    }
}
