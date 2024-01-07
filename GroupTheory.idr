import Syntax.PreorderReasoning
import Data.Nat
import Data.Vect


%default total


infix 8 <>
infix 10 ^


interface Eq g => Group g where
  (<>)      : g -> g -> g
  identityG : g
  inverseG  : (a : g) -> g

  associative   : (a, b, c : g) -> a <> (b <> c) = (a <> b) <> c
  identityLeft  : (a : g) -> identityG <> a = a
  identityRight : (a : g) -> a <> identityG = a
  inverseLeft   : (a : g) -> (inverseG a) <> a = identityG
  inverseRight  : (a : g) -> a <> (inverseG a) = identityG


interface Group g => AbelianGroup where
  commutative : (a : g) -> (b : g) -> a <> b = b <> a


-- show that identity is unique and commutes
rightIdentityIsUnique : Group g => (a, b : g) -> a <> b = a -> b = (identityG {g})
rightIdentityIsUnique a b prf = Calc $
  |~ b
  ~~ (identityG <> b)  ...(sym $ identityLeft b)
  ~~ (((inverseG a) <> a) <> b) ...(rewrite inverseLeft a in Refl)
  ~~ ((inverseG a) <> (a <> b)) ...(sym $ associative (inverseG a) a b)
  ~~ (inverseG a <> a) ...(rewrite prf in Refl)
  ~~ identityG ...(inverseLeft a)


everyIdentityCommutesR : Group g => (a, b : g) -> b <> a = a -> a <> b = a
everyIdentityCommutesR a b prf = Calc $
  |~ a <> b
  ~~ (a <> b) <> identityG ...(sym $ identityRight (a <> b))
  ~~ (a <> b) <> (a <> inverseG a) ...(rewrite inverseRight a in Refl)
  ~~ a <> (b <> (a <> inverseG a)) ...(sym $ associative a b (a <> inverseG a))
  ~~ a <> ((b <> a) <> inverseG a) ...(rewrite (associative b a (inverseG a)) in Refl)
  ~~ a <> (a <> inverseG a) ...(rewrite prf in Refl)
  ~~ a <> identityG ...(rewrite inverseRight a in Refl)
  ~~ a ...(identityRight a)


leftIdentityIsUnique : Group g => (a, b : g) -> b <> a = a -> b = identityG {g}
leftIdentityIsUnique a b prf = rightIdentityIsUnique a b $ everyIdentityCommutesR a b prf


-- show that inverses are unique
leftInverseIsUnique : Group g => (a, b : g) -> b <> a = identityG {g} -> b = (inverseG a)
leftInverseIsUnique a b prf = Calc $
  |~ b
  ~~ b <> (identityG {g}) ...(sym $ identityRight b)
  ~~ b <> (a <> (inverseG a)) ...(rewrite inverseRight a in Refl)
  ~~ (b <> a) <> (inverseG a) ...(associative b a (inverseG a))
  ~~ identityG <> inverseG a ...(rewrite prf in Refl)
  ~~ inverseG a ...(identityLeft $ inverseG a)


everyInverseCommutes : Group g => (a, b : g) -> a <> b = identityG {g} -> b <> a = identityG {g}
everyInverseCommutes a b prf = Calc $
  |~ b <> a
  ~~ (b <> a) <> identityG ...(sym $ identityRight (b <> a))
  ~~ (b <> a) <> (b <> inverseG b) ...(rewrite inverseRight b in Refl)
  ~~ b <> (a <> (b <> inverseG b)) ...(sym $ associative b a (b <> inverseG b))
  ~~ b <> ((a <> b) <> inverseG b) ...(rewrite associative a b (inverseG b) in Refl)
  ~~ b <> (identityG <> inverseG b) ...(rewrite prf in Refl)
  ~~ b <> inverseG b ...(rewrite identityLeft (inverseG b) in Refl)
  ~~ identityG ...(inverseRight b)


rightInverseIsUnique : Group g => (a, b : g) -> a <> b = identityG {g} -> b = (inverseG a)
rightInverseIsUnique a b prf = leftInverseIsUnique a b $ everyInverseCommutes a b prf


-- prove some helpful rules
cancelRight : Group g => (a, b, x : g) -> a <> x = b <> x -> a = b
cancelRight a b x prf = Calc $
  |~ a
  ~~ a <> identityG ...(sym $ identityRight a) 
  ~~ a <> (x <> inverseG x) ...(rewrite inverseRight x in Refl)
  ~~ (a <> x) <> inverseG x ...(associative a x (inverseG x))
  ~~ (b <> x) <> inverseG x ...(rewrite prf in Refl)
  ~~ b <> (x <> inverseG x) ...(sym $ associative b x (inverseG x))
  ~~ b <> identityG ...(rewrite (sym $ inverseRight x) in Refl)
  ~~ b ...(identityRight b)


cancelLeft : Group g => (a, b, x : g) -> x <> a = x <> b -> a = b
cancelLeft a b x prf = Calc $
  |~ a
  ~~ identityG <> a ...(sym $ identityLeft a) 
  ~~ (inverseG x <> x) <> a ...(rewrite inverseLeft x in Refl)
  ~~ inverseG x <> (x <> a) ...(sym $ associative (inverseG x) x a)
  ~~ inverseG x <> (x <> b)...(rewrite prf in Refl)
  ~~ (inverseG x <> x) <> b ...(associative (inverseG x) x b)
  ~~ identityG <> b ...(rewrite inverseLeft x in Refl)
  ~~ b ...(identityLeft b)


-- order specific definitions
powG : Group g => g -> (n : Nat) -> g
powG a 0     = identityG
powG a (S k) = a <> powG a k


(^): Group g => g -> (n : Nat) -> g
(^) = powG


sumExpLaw : {0 grp : Group g} -> (a : g) -> (n : Nat) -> (m : Nat) -> a ^ (n + m) = a ^ n <> a ^ m
sumExpLaw a 0 0 = sym $ identityLeft identityG
sumExpLaw a 0 (S k) = sym $ identityLeft (a <> powG a k)
sumExpLaw a (S k) 0 = Calc $
  |~ a <> a ^ (plus k 0)
  ~~ a <> a ^ k ...(rewrite plusZeroRightNeutral k in Refl)
  ~~ (a <> a ^ k) <> identityG ...(sym $ identityRight $ a <> powG a k)
sumExpLaw a (S k) (S j) = Calc $
  |~ a ^ (S k + S j)
  ~~ a <> (a ^ k <> a ^ (S j)) ...(rewrite sumExpLaw {g} {grp} a k (S j) in Refl)
  ~~ (a ^ (S k)) <> a ^ (S j) ...(associative a (powG a k) (powG a (S j)))


powGMultiplyIdentity : {0 grp : Group g}
  -> (a : g)
  -> (n : Nat) -> a ^ n = identityG {g} -> (x : Nat) -> a ^ (x * n) = identityG {g}
powGMultiplyIdentity a n prf 0 = Refl
powGMultiplyIdentity a n prf (S k) = Calc $
  |~ a ^ ((S k) * n)
  ~~ a ^ (1 * n + k * n) ...(rewrite multDistributesOverPlusLeft 1 k n in Refl)
  ~~ a ^ (1 * n) <> a ^ (k * n) ...(sumExpLaw a (1 * n) (k * n))
  ~~ a ^ n <> a ^ (k * n) ...(rewrite multOneLeftNeutral n in Refl)
  ~~ identityG <> a ^ (k * n) ...(rewrite sym prf in Refl)
  ~~ a ^ (k * n) ...(rewrite identityLeft (a ^ (k * n)) in Refl)
  ~~ identityG ...(powGMultiplyIdentity a n prf k)


interface Group g => Group h => Homomorphic g h where
  funcHom : g -> h
  homomorphism : (x : g) -> (y : g) -> (funcHom x) <> (funcHom y) = funcHom (x <> y)


identityImageActsLikeIdentity : {hmm : Homomorphic g h} -> {b : g} -> funcHom {g} {h} b = funcHom b <> funcHom (identityG {g})
identityImageActsLikeIdentity = Calc $
  |~ funcHom b
  ~~ funcHom (b <> identityG)  ...(rewrite identityRight b in Refl)
  ~~ funcHom b <> funcHom {g} {h} identityG  ...(rewrite sym (homomorphism {g} {h} b identityG) in Refl)


homomorphismMapsIdentity : {hmm : Homomorphic g h} -> funcHom (identityG {g}) = identityG {g = h}
homomorphismMapsIdentity = rightIdentityIsUnique (funcHom identityG) (funcHom {g} {h} identityG) (sym (identityImageActsLikeIdentity {h}))


pullOutExp : {auto hmm : Homomorphic g h} -> {b : g} -> (n : Nat) -> funcHom {g} {h} (b ^ n) = (funcHom b) ^ n
pullOutExp 0 = Calc $
  |~ funcHom (b ^ 0)
  ~~ funcHom identityG  ...(Refl)
  ~~ identityG ...(homomorphismMapsIdentity)
  ~~ funcHom b ^ 0  ...(Refl)
pullOutExp (S k) = Calc $
  |~ funcHom (b ^ (S k))
  ~~ funcHom (b <> b ^ k) ...(Refl)
  ~~ funcHom b <> funcHom (b ^ k) ...(rewrite sym (homomorphism {g} {h} b (b ^ k)) in Refl)
  ~~ funcHom b <> (funcHom b) ^ k ...(rewrite (pullOutExp {g} {h} {b} k) in Refl)
  ~~ funcHom b ^ S k ...(Refl)


homomorphismUpperLimitOrder : {hmm : Homomorphic g h} -> {b : g} -> (n : Nat) -> b ^ n = identityG {g} -> (funcHom {g} {h} b) ^ n = identityG {g = h}
homomorphismUpperLimitOrder n prf = Calc $
  |~ (funcHom b) ^ n
  ~~ funcHom (b ^ n) ...(rewrite sym (pullOutExp {g} {h} {b} n) in Refl)
  ~~ funcHom identityG ...(rewrite prf in Refl)
  ~~ identityG ...(homomorphismMapsIdentity)


-- g should be required to be Eq, don't know how to do this
data FreeGroup : Type -> Type where
  IdentityF  : (g : Type) -> FreeGroup g
  InjectF    : (a : g) -> FreeGroup g
  InverseF   : (a : g) -> FreeGroup g
  MultF      : (a : FreeGroup g) -> (b : FreeGroup g) -> FreeGroup g


Eq g => Eq (FreeGroup g) where
  (==) (IdentityF g) (IdentityF g) = True
  (==) _ (IdentityF g) = False
  (==) (IdentityF g) _ = False
  (==) (InjectF a) (InjectF b) = a == b
  (==) (InjectF a) (InverseF x) = False
  (==) (InjectF a) (MultF x b) = False
  (==) (InverseF a) (InverseF b) = a == b
  (==) (InverseF a) _ = False
  (==) (MultF a x) (MultF b y) = a == b && x == y 
  (==) (MultF a x) _ = False


freeGroupMult : {g : Type} -> Eq g => FreeGroup g -> FreeGroup g -> FreeGroup g
freeGroupMult x (IdentityF g) = x
freeGroupMult (IdentityF g) y = y
freeGroupMult a'@(InjectF a) b'@(InjectF b) = MultF a' b'
freeGroupMult a'@(InjectF a) b'@(InverseF b) = case a == b of
                                              False => MultF a' b'
                                              True => IdentityF g
freeGroupMult a'@(InjectF a) b'@(MultF x b) = MultF a' b'
freeGroupMult a'@(InverseF a) b'@(InjectF x) = case a == x of
                                              False => MultF a' b'
                                              True => IdentityF g
freeGroupMult a'@(InverseF a) z = MultF a' z
freeGroupMult a'@(MultF a b) b'@(MultF x y) = case b of
  (InverseF z) => case x of
    (InjectF w) => case z == w of
      False => MultF a' b'
      -- b and x are inverses
      True => freeGroupMult a y
    _ => MultF a' b'
  (InjectF z) => case x of
    (InverseF w) => case z == w of
      False => MultF a' b'
      -- b and x are inverses
      True => freeGroupMult a y
    _ => MultF a' b'
  _ => MultF a' b'
freeGroupMult a'@(MultF a b) y = MultF a' y


{g : Type} -> Eq g => Group (FreeGroup g) where
  (<>)      = freeGroupMult
  identityG = IdentityF g
  inverseG a = case a of
                    e@(IdentityF g) => e
                    (InjectF x) => InverseF x
                    (InverseF x) => InjectF x
                    (MultF x b) => (MultF (inverseG x) (inverseG b))
  -- good luck with this...
  associative   = ?c
  identityLeft  = ?e
  identityRight = ?f
  inverseLeft   = ?g
  inverseRight  = ?h
