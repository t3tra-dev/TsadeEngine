#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Ty {
    Atom(u32),
    Arr(Box<Ty>, Box<Ty>),
    Prod(Box<Ty>, Box<Ty>),
    Sum(Box<Ty>, Box<Ty>),
    Bot,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Tm {
    Var(u32),
    Lam {
        arg_ty: Ty,
        body: Box<Tm>,
    },
    App(Box<Tm>, Box<Tm>),
    Pair(Box<Tm>, Box<Tm>),
    Fst(Box<Tm>),
    Snd(Box<Tm>),
    Inl {
        rhs_ty: Ty,
        term: Box<Tm>,
    },
    Inr {
        lhs_ty: Ty,
        term: Box<Tm>,
    },
    Case {
        scrut: Box<Tm>,
        left: Box<Tm>,
        right: Box<Tm>,
    },
    Absurd {
        bot_term: Box<Tm>,
        target_ty: Ty,
    },
}

pub type Ctx = Vec<Ty>;

pub fn ty_size(ty: &Ty) -> usize {
    match ty {
        Ty::Atom(_) => 1,
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => 1 + ty_size(a) + ty_size(b),
        Ty::Bot => 1,
    }
}
