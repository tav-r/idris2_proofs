import Debug.Trace


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


{- section 4 -}

-- catamorphism, anamorphism, hylomorphism
{-Notice the direct use of recursion instead of using a fixed point operator
(like in the paper).

Furthermore, the value 'inside' the functor has to be made evaluated lazy
in order for the program to see, for example when calculating the length
of a ConsList, the step

`(f . (cata alg) . Out) (In NilF)`

as

`f (NilF) = 0`

and evaluate it to 0 and prevent it from continuing to unfold.
-}
partial
cata : Functor f => (f (Lazy b) -> b) -> Mu f -> b
cata alg = (alg <%- Out) (delay . cata alg)


partial
ana : Functor f => (b -> f b) -> b -> Mu f
ana coalg = (In <%- coalg) (ana coalg)


partial
hylo : Functor f => (f c -> c) -> (b -> f b) -> b -> c
hylo alg coalg = (alg <%- coalg) (hylo alg coalg)


{- examples -}

-- cons list
data ListF a r = NilF | ConsF a r


Functor (ListF a) where
  map f NilF = NilF
  map f (ConsF x y) = ConsF x (f y)


ConsList : Type -> Type
ConsList e = Mu (ListF e)


infixr 2 :::
(:::) : a -> ConsList a -> ConsList a
(:::) x y = In (ConsF x y)


Empty : ConsList a
Empty = In NilF


consToList : ConsList e -> List e
consToList (In NilF) = []
consToList (In (ConsF e rest)) = e :: consToList rest


test : {T : Type} -> {a, b, c : T} -> consToList (a ::: b ::: c ::: Empty) = [a, b, c]
test = Refl


partial
length : ConsList a -> Nat
length = cata f
  where
    f : ListF a (Lazy Nat) -> Nat
    f NilF = 0
    f (ConsF _ n) = 1 + force n


partial
main : IO ()
main = do
  printLn $ Main.length (1 ::: 2 ::: 3 ::: Empty)
