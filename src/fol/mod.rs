use crate::kernel::{FOTerm, Ty, fo_term_shift, fo_term_size};

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

pub fn formula_term_subst(j: u32, s: &FOTerm, fm: &FOFormula) -> FOFormula {
    fn term_walk(c: u32, j: u32, s: &FOTerm, tm: &FOTerm) -> FOTerm {
        match tm {
            FOTerm::Var(i) => {
                if *i == j + c {
                    fo_term_shift(c as i32, 0, s)
                } else {
                    FOTerm::Var(*i)
                }
            }
            FOTerm::Const(k) => FOTerm::Const(*k),
            FOTerm::Func { sym, args } => FOTerm::Func {
                sym: *sym,
                args: args.iter().map(|a| term_walk(c, j, s, a)).collect(),
            },
        }
    }

    fn walk(c: u32, j: u32, s: &FOTerm, fm: &FOFormula) -> FOFormula {
        match fm {
            FOFormula::Pred { sym, args } => FOFormula::Pred {
                sym: *sym,
                args: args.iter().map(|a| term_walk(c, j, s, a)).collect(),
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
        FOFormula::Pred { args, .. } => 1 + args.iter().map(fo_term_size).sum::<usize>(),
        FOFormula::Bot => 1,
        FOFormula::Arr(a, b) | FOFormula::Prod(a, b) | FOFormula::Sum(a, b) => {
            1 + formula_size(a) + formula_size(b)
        }
        FOFormula::Forall(x) | FOFormula::Exists(x) => 1 + formula_size(x),
    }
}

/// FOFormula DSL の値をカーネルの Ty 表現に変換
pub fn formula_to_ty(fm: &FOFormula) -> Ty {
    match fm {
        FOFormula::Pred { sym, args } => Ty::Pred {
            sym: *sym,
            args: args.clone(),
        },
        FOFormula::Bot => Ty::Bot,
        FOFormula::Arr(a, b) => Ty::Arr(Box::new(formula_to_ty(a)), Box::new(formula_to_ty(b))),
        FOFormula::Prod(a, b) => Ty::Prod(Box::new(formula_to_ty(a)), Box::new(formula_to_ty(b))),
        FOFormula::Sum(a, b) => Ty::Sum(Box::new(formula_to_ty(a)), Box::new(formula_to_ty(b))),
        FOFormula::Forall(body) => Ty::Forall(Box::new(formula_to_ty(body))),
        FOFormula::Exists(body) => Ty::Exists(Box::new(formula_to_ty(body))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_shift_basic() {
        assert_eq!(fo_term_shift(1, 0, &FOTerm::Var(0)), FOTerm::Var(1));
        assert_eq!(fo_term_shift(1, 1, &FOTerm::Var(0)), FOTerm::Var(0));
    }

    #[test]
    fn term_subst_top_basic() {
        use crate::kernel::fo_term_subst_top;
        let body = FOTerm::Var(0);
        let arg = FOTerm::Const(7);
        assert_eq!(fo_term_subst_top(&arg, &body), FOTerm::Const(7));
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

    /// 回帰: 量化子における `formula_term_subst` は自由変数を正しく置換し束縛変数をそのままにする必要がある
    ///
    /// expr: ∀. P(Var(1)) - Var(0) は ∀ によって束縛され Var(1) は自由変数 (= 元のVar(0))
    /// j=0 を Const(42) で置換:
    ///   期待値: ∀. P(Const(42))
    ///   BUG (old code): Var(1) を c=1 だけ pre-shift して Var(2) にしその後 j+c=1 を置換する (一致しない) → Var(2) のまま
    #[test]
    fn formula_term_subst_under_quantifier() {
        // ∀. P(Var(1))  — free var 0 appears as Var(1) under one binder
        let fm = FOFormula::Forall(Box::new(FOFormula::Pred {
            sym: 0,
            args: vec![FOTerm::Var(1)],
        }));
        let result = formula_term_subst(0, &FOTerm::Const(42), &fm);
        let expected = FOFormula::Forall(Box::new(FOFormula::Pred {
            sym: 0,
            args: vec![FOTerm::Const(42)],
        }));
        assert_eq!(result, expected);
    }

    /// 量化子の束縛変数が置換されないようにする
    #[test]
    fn formula_term_subst_bound_var_preserved() {
        // ∀. P(Var(0)) - Var(0) は ∀ によって束縛される
        let fm = FOFormula::Forall(Box::new(FOFormula::Pred {
            sym: 0,
            args: vec![FOTerm::Var(0)],
        }));
        let result = formula_term_subst(0, &FOTerm::Const(42), &fm);
        // 変更不可 - 束縛変数は置換してはならない
        assert_eq!(result, fm);
    }

    #[test]
    fn formula_to_ty_roundtrip() {
        let fm = FOFormula::Forall(Box::new(FOFormula::Arr(
            Box::new(FOFormula::Pred {
                sym: 0,
                args: vec![FOTerm::Var(0)],
            }),
            Box::new(FOFormula::Exists(Box::new(FOFormula::Pred {
                sym: 1,
                args: vec![FOTerm::Var(0), FOTerm::Var(1)],
            }))),
        )));
        let ty = formula_to_ty(&fm);
        let expected = Ty::Forall(Box::new(Ty::Arr(
            Box::new(Ty::Pred {
                sym: 0,
                args: vec![FOTerm::Var(0)],
            }),
            Box::new(Ty::Exists(Box::new(Ty::Pred {
                sym: 1,
                args: vec![FOTerm::Var(0), FOTerm::Var(1)],
            }))),
        )));
        assert_eq!(ty, expected);
    }
}
