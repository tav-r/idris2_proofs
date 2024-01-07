data State = StateF Char

data Proposition : Char -> Type where
  Prop : (c : Char) -> Proposition c

-- frame requirements for S5
data Sees : State -> State -> Type where
  Reflexive  : (v : State) -> Sees v v          -- for T
  Transitive : Sees u v -> Sees v w -> Sees u w -- for A4
  Euclidean  : Sees u v -> Sees u w -> Sees v w -- for A5

-- empty types for modal operators
data Box : Type -> Type where
data Diamond : Type -> Type where

-- construction rules for (valid) formulas
data Formula : State -> Type -> Type where
  Atom    : (w : State) -> Proposition c -> Formula w (Proposition c)
  And     : (w : State) -> (p : Formula w a) -> (q : Formula w b) -> Formula w (a, b)
  Or      : (w : State) -> Either (Formula w a) (Formula w b) -> Formula w (Either a b)
  Implies : (w : State) -> (Formula w a -> Formula w b) -> Formula w (a -> b)
  Nec     : (v : State) -> ((w : State) -> Sees v w -> Formula w a) -> Formula v (Box a)
  Poss    : (v : State) -> (w : State ** (Sees v w, Formula w a)) -> Formula v (Diamond a)

-- rules
mp : Formula w (a -> b) -> Formula w a -> Formula w b
mp (Implies _ f) y = f y

-- axioms
K : Formula v (Box (a -> b)) -> Formula v (Box a) -> Formula v (Box b)
K (Nec v f) (Nec v g) = let p = \w => \s => mp (f w s) (g w s) in Nec v p

T : Formula v (Box a) -> Formula v a
T (Nec v f) = (f v) (Reflexive v)

A4 : Formula v (Box a) -> Formula v (Box (Box a))
A4 (Nec v f) = Nec v (\w => \x => Nec w (\y => \z => f y (Transitive x z)))

A5 : Formula v (Diamond a) -> Formula v (Box (Diamond a))
A5 (Poss v ((w ** (x, y)))) = Nec v \u => \z => Poss u (w ** (Euclidean z x, y))
