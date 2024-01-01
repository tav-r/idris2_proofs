import System
import Data.List
import Data.String


%default total


{- section 3 -}

-- functor stuff
infix 1 -%>
(-%>) : Functor f => (a -> f b) -> (f c -> d) -> (b -> c) -> (a -> d)
(-%>) f g h = g . map h . f


infix 1 <%-
(<%-) : Functor f => (f c -> d) -> (a -> f b) -> (b -> c) -> (a -> d)
(<%-) = flip (-%>)


-- fixed points
partial
data Mu : (f : Type -> Type) -> Type where
  In : Functor f => f (Mu f) -> Mu f


Out : Mu f -> f (Mu f)
Out (In x) = x


{- section 4: catamorphism, anamorphism, hylomorphism -}

{-
Furthermore, the value 'inside' the functor has to be made evaluated lazy
in order for the program to see, for example when calculating the length
of a ConsList, the step
`(f . (cata alg) . Out) (In NilF)`
as
`f (NilF) = 0`
and evaluate it to 0 and prevent it from continuing to unfold.-}
partial
cata : Functor f => (f (Lazy b) -> b) -> Mu f -> b
cata alg = (alg <%- Out) (delay . cata alg)


partial
ana : Functor f => (b -> f b) -> b -> Mu f
ana coalg = (In <%- coalg) (ana coalg)


partial
hylo : Functor f => (f (Lazy c) -> c) -> (b -> f b) -> b -> c
hylo alg coalg = (alg <%- coalg) (delay . hylo alg coalg)


{- examples -}

-- cons list
data ListF a r = NilF | ConsF a r


Functor (ListF a) where
  map f NilF = NilF
  map f (ConsF x y) = ConsF x (f y)


-- a `ConsList a` is a fixed point of the functor `ListF a`
ConsList : Type -> Type
ConsList a = Mu (ListF a)


infixr 2 :::
(:::) : a -> ConsList a -> ConsList a
(:::) x y = In (ConsF x y)


Empty : ConsList a
Empty = In NilF


consToList : ConsList e -> List e
consToList (In NilF) = []
consToList (In (ConsF e rest)) = e :: consToList rest


appendingIsEquivalent : {T : Type} -> {a : T} -> (xs : ConsList T)
  -> (xs' : List T) -> consToList xs = xs' -> consToList (a ::: xs) = a :: xs'
appendingIsEquivalent xs xs' prf = rewrite (sym prf) in Refl


partial
length : ConsList a -> Nat
length = cata alg
  where
    alg : ListF a (Lazy Nat) -> Nat
    alg NilF = 0
    alg (ConsF _ n) = 1 + force n


test1 : {T : Type} -> {a, b, c : T} -> length (a ::: b ::: c ::: Empty) = 3
test1 = Refl


fibExpand : (Nat, Nat, Nat) -> ListF Nat (Nat, Nat, Nat)
fibExpand (a, b, 0) = NilF
fibExpand (a, b, S n) = ConsF a (b, a + b, n)


fibCollapse : ListF Nat (Lazy Nat) -> Nat
fibCollapse NilF = 0
fibCollapse (ConsF x y) = max x y


partial
fibHylo : Nat -> Nat
fibHylo n = hylo fibCollapse fibExpand (0, 1, n + 2)


-- natural numbers
data NatF n = ZeroF | SuccF n


Functor NatF where
  map f ZeroF = ZeroF
  map f (SuccF x) = SuccF (f x)


partial
Nat' : Type
Nat' = Mu NatF


partial
main : IO ()
main = printLn =<< map fibHylo . (=<<) parsePositive . head' . drop 1 <$> getArgs
