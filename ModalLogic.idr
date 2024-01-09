%default total

data Ty : Type where
  Prop   : Type -> Ty
  Imp    : Ty -> Ty -> Ty
  Disj   : Ty -> Ty -> Ty
  Conj   : Ty -> Ty -> Ty
  Boxed  : Ty -> Ty

-- construction rules for (valid) formulas as PHOAS, see for example
-- https://leanprover.github.io/lean4/doc/examples/phoas.lean.html
data Formula' : (Ty -> Type) -> Ty -> Type where
  -- types as propositions
  Atom    : (rep : Ty -> Type) -> (a : Type) -> Formula' rep $ Prop a

  -- intuitionistic axioms
  And     : (rep : Ty -> Type) -> rep c1 -> rep c2 -> Formula' rep $ Conj c1 c2
  Or      : (rep : Ty -> Type) -> Either (rep d1) (rep d2) -> Formula' rep $ Disj d1 d2
  Implies : (rep : Ty -> Type) -> (rep ant -> rep con) -> Formula' rep $ Imp ant con

  -- modal axioms
  K       : (rep : Ty -> Type) -> Formula' rep (Boxed (Imp a b)) -> Formula' rep (Boxed a) -> Formula' rep (Boxed b)
  A4      : (rep : Ty -> Type) -> Formula' rep (Boxed a) -> Formula' rep (Boxed (Boxed a))

  -- inference rules
  Mp      : (rep : Ty -> Type) -> Formula' rep (Imp a b) -> Formula' rep a -> Formula' rep b
  Nec     : (rep : Ty -> Type) -> Formula' rep a -> Formula' rep (Boxed a)

mutual
  data Box : Type -> Type where
    MkBox : Formula a -> Box (denote a)
    BoxK  : Box (a -> b) -> Box a -> Box b
    Box4  : Box a -> Box (Box a)

  denote : Ty -> Type
  denote (Prop a)     = Type
  denote (Conj c1 c2) = (denote c1, denote c2) 
  denote (Disj d1 d2) = Either (denote d1) (denote d2)
  denote (Imp x y)    = denote x -> denote y
  denote (Boxed x)    = Box (denote x)

  Formula : (ty : Ty) -> Type
  Formula = Formula' denote

denoteFormula : Formula ty -> denote ty
denoteFormula (Atom _ c) = c
denoteFormula (And _ a b) = (a, b)
denoteFormula (Or _ d) = d
denoteFormula (Implies _ f) = f
denoteFormula (Mp _ f a) = (denoteFormula f) (denoteFormula a)
denoteFormula (Nec _ a) = MkBox a
denoteFormula (K _ a b) = BoxK (denoteFormula a) (denoteFormula b)
denoteFormula (A4 _ a) = Box4 (denoteFormula a)

-- maps back to basic types using the Gödel-McKinsey-Tarski translation
denoteGMK: Ty -> Type
denoteGMK (Prop a) = Type
denoteGMK (Imp a b) = denoteGMK a -> denoteGMK b
denoteGMK (Disj a b) = Either (denoteGMK a) (denoteGMK b)
denoteGMK (Conj a b) = (denoteGMK a, denoteGMK b)
denoteGMK (Boxed a) = denoteGMK a

FormulaGMK : (ty : Ty) -> Type
FormulaGMK = Formula' denoteGMK

denoteFormulaGMK : FormulaGMK ty -> denoteGMK ty
denoteFormulaGMK (Atom _ c) = c
denoteFormulaGMK (And _ a b) = (a, b)
denoteFormulaGMK (Or _ d) = d
denoteFormulaGMK (Implies _ f) = f
denoteFormulaGMK (Mp _ f a) = (denoteFormulaGMK f) (denoteFormulaGMK a)
denoteFormulaGMK (Nec _ a) = denoteFormulaGMK a
denoteFormulaGMK (K _ a b) = (denoteFormulaGMK a) (denoteFormulaGMK b)
denoteFormulaGMK (A4 _ a) = denoteFormulaGMK a
