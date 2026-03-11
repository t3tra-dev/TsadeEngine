use std::fmt;

use super::ops::{ty_term_free_in, ty_term_shift, ty_term_subst_top};
use super::{Ctx, Tm, Ty};

/// 型の正規化
///
/// 命題論理の型には β-redex が存在しないため現在は恒等関数だが
/// FOL 拡張で型中に項 (`Pred { args }`) が埋め込まれた場合にここで項引数を正規化する拡張点となる
pub fn normalize_ty(ty: &Ty) -> Ty {
    match ty {
        Ty::Atom(i) => Ty::Atom(*i),
        Ty::Bot => Ty::Bot,
        Ty::Pred { sym, args } => Ty::Pred {
            sym: *sym,
            args: args.clone(),
        },
        Ty::Arr(a, b) => Ty::Arr(Box::new(normalize_ty(a)), Box::new(normalize_ty(b))),
        Ty::Prod(a, b) => Ty::Prod(Box::new(normalize_ty(a)), Box::new(normalize_ty(b))),
        Ty::Sum(a, b) => Ty::Sum(Box::new(normalize_ty(a)), Box::new(normalize_ty(b))),
        Ty::Forall(body) => Ty::Forall(Box::new(normalize_ty(body))),
        Ty::Exists(body) => Ty::Exists(Box::new(normalize_ty(body))),
        Ty::Eq(s, t) => Ty::Eq(s.clone(), t.clone()),
    }
}

/// 型の同値判定
///
/// 両辺を `normalize_ty` で正規化したうえで構造比較する
/// 命題論理では `==` と等価だが、FOL 拡張時に型中の項が β 同値なケース (`P((\x.x) t)` vs `P(t)`) を吸収する
pub fn ty_equiv(a: &Ty, b: &Ty) -> bool {
    normalize_ty(a) == normalize_ty(b)
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypeError {
    UnboundVar { index: u32, ctx_len: usize },
    NotAFunction { found: Box<Ty> },
    ArgTypeMismatch { expected: Box<Ty>, found: Box<Ty> },
    NotAProduct { found: Box<Ty> },
    NotASum { found: Box<Ty> },
    NotBot { found: Box<Ty> },
    BranchTypeMismatch { left: Box<Ty>, right: Box<Ty> },
    TypeMismatch { expected: Box<Ty>, found: Box<Ty> },
    NotAForall { found: Box<Ty> },
    NotAnExists { found: Box<Ty> },
    NotAnEquality { found: Box<Ty> },
    TermVarEscapes,
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
            TypeError::NotAForall { found } => {
                write!(f, "expected forall type, found {found:?}")
            }
            TypeError::NotAnExists { found } => {
                write!(f, "expected exists type, found {found:?}")
            }
            TypeError::NotAnEquality { found } => {
                write!(f, "expected equality type, found {found:?}")
            }
            TypeError::TermVarEscapes => {
                write!(f, "term variable escapes its scope in unpack")
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
                    if ty_equiv(&arg, &x_ty) {
                        Ok(*out)
                    } else {
                        Err(TypeError::ArgTypeMismatch {
                            expected: arg,
                            found: Box::new(x_ty),
                        })
                    }
                }
                other => Err(TypeError::NotAFunction {
                    found: Box::new(other),
                }),
            }
        }
        Tm::Pair(a, b) => {
            let a_ty = infer(ctx, a)?;
            let b_ty = infer(ctx, b)?;
            Ok(Ty::Prod(Box::new(a_ty), Box::new(b_ty)))
        }
        Tm::Fst(t) => match infer(ctx, t)? {
            Ty::Prod(a, _) => Ok(*a),
            other => Err(TypeError::NotAProduct {
                found: Box::new(other),
            }),
        },
        Tm::Snd(t) => match infer(ctx, t)? {
            Ty::Prod(_, b) => Ok(*b),
            other => Err(TypeError::NotAProduct {
                found: Box::new(other),
            }),
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
                if ty_equiv(&lty, &rty) {
                    Ok(lty)
                } else {
                    Err(TypeError::BranchTypeMismatch {
                        left: Box::new(lty),
                        right: Box::new(rty),
                    })
                }
            }
            other => Err(TypeError::NotASum {
                found: Box::new(other),
            }),
        },
        Tm::Absurd {
            bot_term,
            target_ty,
        } => match infer(ctx, bot_term)? {
            Ty::Bot => Ok(target_ty.clone()),
            other => Err(TypeError::NotBot {
                found: Box::new(other),
            }),
        },
        Tm::TLam { body } => {
            // ∀-intro: shift all ctx types up by 1 term var, infer body, wrap in Forall
            let shifted_ctx: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
            let body_ty = infer(&shifted_ctx, body)?;
            Ok(Ty::Forall(Box::new(body_ty)))
        }
        Tm::TApp { term, witness } => {
            // ∀-elim: term must have type ∀.φ, result is φ[0:=witness]
            match infer(ctx, term)? {
                Ty::Forall(body) => Ok(ty_term_subst_top(witness, &body)),
                other => Err(TypeError::NotAForall {
                    found: Box::new(other),
                }),
            }
        }
        Tm::Pack {
            witness,
            body,
            exists_ty,
        } => {
            // ∃-intro: exists_ty must be ∃.φ, body must have type φ[0:=witness]
            match exists_ty {
                Ty::Exists(phi) => {
                    let expected = ty_term_subst_top(witness, phi);
                    let body_ty = infer(ctx, body)?;
                    if ty_equiv(&body_ty, &expected) {
                        Ok(exists_ty.clone())
                    } else {
                        Err(TypeError::TypeMismatch {
                            expected: Box::new(expected),
                            found: Box::new(body_ty),
                        })
                    }
                }
                _ => Err(TypeError::NotAnExists {
                    found: Box::new(exists_ty.clone()),
                }),
            }
        }
        Tm::Refl { term } => Ok(Ty::Eq(term.clone(), term.clone())),
        Tm::Subst {
            eq_proof,
            body,
            motive,
        } => match infer(ctx, eq_proof)? {
            Ty::Eq(lhs, rhs) => {
                let body_ty = infer(ctx, body)?;
                let expected = ty_term_subst_top(&lhs, motive);
                if ty_equiv(&body_ty, &expected) {
                    Ok(ty_term_subst_top(&rhs, motive))
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: Box::new(expected),
                        found: Box::new(body_ty),
                    })
                }
            }
            other => Err(TypeError::NotAnEquality {
                found: Box::new(other),
            }),
        },
        Tm::Unpack { scrut, body } => {
            // ∃-elim: scrut must have type ∃.φ,
            // body checked in extended context (shift ctx up by 1 term var, push φ),
            // body type must not mention term var 0, then shift result down
            match infer(ctx, scrut)? {
                Ty::Exists(phi) => {
                    let shifted_ctx: Ctx = ctx.iter().map(|t| ty_term_shift(1, 0, t)).collect();
                    let mut ext = shifted_ctx;
                    ext.push(*phi);
                    let body_ty = infer(&ext, body)?;
                    if ty_term_free_in(0, &body_ty) {
                        Err(TypeError::TermVarEscapes)
                    } else {
                        Ok(ty_term_shift(-1, 0, &body_ty))
                    }
                }
                other => Err(TypeError::NotAnExists {
                    found: Box::new(other),
                }),
            }
        }
    }
}

pub fn check(ctx: &Ctx, tm: &Tm, ty: &Ty) -> Result<(), TypeError> {
    let inferred = infer(ctx, tm)?;
    if ty_equiv(&inferred, ty) {
        Ok(())
    } else {
        Err(TypeError::TypeMismatch {
            expected: Box::new(ty.clone()),
            found: Box::new(inferred),
        })
    }
}
