#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum FOTerm {
    Var(u32),
    Const(u32),
    Func { sym: u32, args: Vec<FOTerm> },
}

pub fn fo_term_size(tm: &FOTerm) -> usize {
    match tm {
        FOTerm::Var(_) | FOTerm::Const(_) => 1,
        FOTerm::Func { args, .. } => 1 + args.iter().map(fo_term_size).sum::<usize>(),
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Ty {
    Atom(u32),
    Pred { sym: u32, args: Vec<FOTerm> },
    Arr(Box<Ty>, Box<Ty>),
    Prod(Box<Ty>, Box<Ty>),
    Sum(Box<Ty>, Box<Ty>),
    Forall(Box<Ty>),
    Exists(Box<Ty>),
    Bot,
    Eq(FOTerm, FOTerm),
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
    TLam {
        body: Box<Tm>,
    },
    TApp {
        term: Box<Tm>,
        witness: FOTerm,
    },
    Pack {
        witness: FOTerm,
        body: Box<Tm>,
        exists_ty: Ty,
    },
    Unpack {
        scrut: Box<Tm>,
        body: Box<Tm>,
    },
    Refl {
        term: FOTerm,
    },
    Subst {
        eq_proof: Box<Tm>,
        body: Box<Tm>,
        motive: Ty,
    },
}

pub type Ctx = Vec<Ty>;

pub fn ty_size(ty: &Ty) -> usize {
    match ty {
        Ty::Atom(_) => 1,
        Ty::Pred { args, .. } => 1 + args.iter().map(fo_term_size).sum::<usize>(),
        Ty::Arr(a, b) | Ty::Prod(a, b) | Ty::Sum(a, b) => 1 + ty_size(a) + ty_size(b),
        Ty::Forall(body) | Ty::Exists(body) => 1 + ty_size(body),
        Ty::Bot => 1,
        Ty::Eq(s, t) => 1 + fo_term_size(s) + fo_term_size(t),
    }
}
