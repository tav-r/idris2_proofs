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


sumExpLaw : {0 g : Type} -> {0 grp : Group g} -> (a : g) -> (n : Nat) -> (m : Nat) -> a ^ (n + m) = a ^ n <> a ^ m
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


powGMultiplyIdentity : {0 g : Type}
  -> {0 grp : Group g}
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


identityImageActsLikeIdentity : {auto hmm : Homomorphic g h} -> {b : g} -> funcHom {g} {h} b = funcHom b <> funcHom (identityG {g})
identityImageActsLikeIdentity = Calc $
  |~ funcHom b
  ~~ funcHom (b <> identityG)  ...(rewrite identityRight b in Refl)
  ~~ funcHom b <> funcHom {g} {h} identityG  ...(rewrite sym (homomorphism {g} {h} b identityG) in Refl)


homomorphismMapsIdentity : {auto hmm : Homomorphic g h} -> {b : g} -> funcHom (identityG {g}) = (identityG {g = h})
homomorphismMapsIdentity = rightIdentityIsUnique (funcHom b) (funcHom {g} {h} identityG) (sym (identityImageActsLikeIdentity {h}))
