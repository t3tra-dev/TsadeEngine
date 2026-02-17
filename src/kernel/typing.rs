use std::fmt;

use super::{Ctx, Tm, Ty};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypeError {
    UnboundVar { index: u32, ctx_len: usize },
    NotAFunction { found: Ty },
    ArgTypeMismatch { expected: Ty, found: Ty },
    NotAProduct { found: Ty },
    NotASum { found: Ty },
    NotBot { found: Ty },
    BranchTypeMismatch { left: Ty, right: Ty },
    TypeMismatch { expected: Ty, found: Ty },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVar { index, ctx_len } => {
                write!(
                    f,
                    "unbound variable Var({index}) in context length {ctx_len}"
                )
            }
            TypeError::NotAFunction { found } => {
                write!(f, "expected function type, found {found:?}")
            }
            TypeError::ArgTypeMismatch { expected, found } => {
                write!(
                    f,
                    "application argument mismatch: expected {expected:?}, found {found:?}"
                )
            }
            TypeError::NotAProduct { found } => write!(f, "expected product type, found {found:?}"),
            TypeError::NotASum { found } => write!(f, "expected sum type, found {found:?}"),
            TypeError::NotBot { found } => write!(f, "expected Bot, found {found:?}"),
            TypeError::BranchTypeMismatch { left, right } => {
                write!(f, "case branch mismatch: left={left:?} right={right:?}")
            }
            TypeError::TypeMismatch { expected, found } => {
                write!(f, "type mismatch: expected {expected:?}, found {found:?}")
            }
        }
    }
}

impl std::error::Error for TypeError {}

pub fn ctx_lookup(ctx: &Ctx, i: u32) -> Option<&Ty> {
    let idx = i as usize;
    if idx >= ctx.len() {
        return None;
    }
    let reverse_idx = ctx.len() - 1 - idx;
    ctx.get(reverse_idx)
}

pub fn infer(ctx: &Ctx, tm: &Tm) -> Result<Ty, TypeError> {
    match tm {
        Tm::Var(i) => ctx_lookup(ctx, *i).cloned().ok_or(TypeError::UnboundVar {
            index: *i,
            ctx_len: ctx.len(),
        }),
        Tm::Lam { arg_ty, body } => {
            let mut ext = ctx.clone();
            ext.push(arg_ty.clone());
            let body_ty = infer(&ext, body)?;
            Ok(Ty::Arr(Box::new(arg_ty.clone()), Box::new(body_ty)))
        }
        Tm::App(f, x) => {
            let f_ty = infer(ctx, f)?;
            let x_ty = infer(ctx, x)?;
            match f_ty {
                Ty::Arr(arg, out) => {
                    if *arg == x_ty {
                        Ok(*out)
                    } else {
                        Err(TypeError::ArgTypeMismatch {
                            expected: *arg,
                            found: x_ty,
                        })
                    }
                }
                other => Err(TypeError::NotAFunction { found: other }),
            }
        }
        Tm::Pair(a, b) => {
            let a_ty = infer(ctx, a)?;
            let b_ty = infer(ctx, b)?;
            Ok(Ty::Prod(Box::new(a_ty), Box::new(b_ty)))
        }
        Tm::Fst(t) => match infer(ctx, t)? {
            Ty::Prod(a, _) => Ok(*a),
            other => Err(TypeError::NotAProduct { found: other }),
        },
        Tm::Snd(t) => match infer(ctx, t)? {
            Ty::Prod(_, b) => Ok(*b),
            other => Err(TypeError::NotAProduct { found: other }),
        },
        Tm::Inl { rhs_ty, term } => {
            let lhs_ty = infer(ctx, term)?;
            Ok(Ty::Sum(Box::new(lhs_ty), Box::new(rhs_ty.clone())))
        }
        Tm::Inr { lhs_ty, term } => {
            let rhs_ty = infer(ctx, term)?;
            Ok(Ty::Sum(Box::new(lhs_ty.clone()), Box::new(rhs_ty)))
        }
        Tm::Case { scrut, left, right } => match infer(ctx, scrut)? {
            Ty::Sum(a, b) => {
                let mut lctx = ctx.clone();
                lctx.push((*a).clone());
                let lty = infer(&lctx, left)?;
                let mut rctx = ctx.clone();
                rctx.push((*b).clone());
                let rty = infer(&rctx, right)?;
                if lty == rty {
                    Ok(lty)
                } else {
                    Err(TypeError::BranchTypeMismatch {
                        left: lty,
                        right: rty,
                    })
                }
            }
            other => Err(TypeError::NotASum { found: other }),
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => match infer(ctx, bot_term)? {
            Ty::Bot => Ok(target_ty.clone()),
            other => Err(TypeError::NotBot { found: other }),
        },
    }
}

pub fn check(ctx: &Ctx, tm: &Tm, ty: &Ty) -> Result<(), TypeError> {
    let inferred = infer(ctx, tm)?;
    if &inferred == ty {
        Ok(())
    } else {
        Err(TypeError::TypeMismatch {
            expected: ty.clone(),
            found: inferred,
        })
    }
}
