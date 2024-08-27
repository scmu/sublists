{-
  Haskell implementation of some of the functions in

    Bottom-Up Computation Using Trees of Sublists.
    Shin-Cheng Mu, 2024.

  In this file we use cons lists in the specification,
  but construct an |up| that uses snoc in its implementation,
  hence the name of this file.
-}

import Prelude hiding (repeat)

-- Sublists and Choose

type Nat = Int
type L a = [a]

subs :: L a -> L (L a)
subs []      = []
subs (x:xs)  = map (x:) (subs xs) ++ [xs]

choose :: Nat -> L a -> L (L a)
choose 0  _       =  [[]]
choose k  xs      |  k == length xs = [xs]
choose k  (x:xs)  =  map (x:) (choose (k-1) xs) ++ choose k xs

-- The Binomial Tree

data B a = T a | N (B a) (B a)
  deriving (Eq, Show)

unT :: B a -> a
unT (T x) = x

mapB   :: (a -> b) -> B a -> B b
mapB f (T x)   = T (f x)
mapB f (N t u) = N (mapB f t) (mapB f u)

zipBW  :: (a -> b -> c) -> B a -> B b -> B c
zipBW f (T x) (T y) = T (f x y)
zipBW f (N t0 u0) (N t1 u1) = N (zipBW f t0 t1) (zipBW f u0 u1)

ch :: Nat -> L a -> B (L a)
ch 0  _       =  T []
ch k  xs      |  k == length xs = T xs
ch k  (x:xs)  =  N (mapB (x:) (ch (k-1) xs)) (ch k xs)

snoc :: L a -> a -> L a
snoc xs x = xs ++ [x]

-- Up

up :: B a -> B (L a)
up (N (T p)  (T q)  ) = T [p,q]
up (N t      (T q)  ) = T (unT (up t) ++ [q])
up (N (T p)  u      ) = N (mapB (\q -> [p,q]) u) (up u)
up (N t      u      ) = N (zipBW snoc (up t) u) (up u)

-- The Top-Down Algorithm

h :: L X -> Y
h xs = td (length xs - 1) xs

ex :: L a -> a
ex [x] = x

td :: Nat -> L X -> Y
td 0 = f . ex
td n = g . map (td (n-1)) . subs

td' :: Nat -> L Y -> Y
td' 0 = ex
td' n = g . map (td' (n-1)) . subs

-- The Bottom-Up Algorithm

repeat :: Nat -> (a -> a) -> a -> a
repeat 0 f = id
repeat n f = repeat (n-1) f . f

bu :: Nat -> L X -> Y
bu n = unT . repeat n (mapB g . up) . mapB ex . ch 1 . map f

  -- defined to observe a level in the middle

bu' :: Nat -> L X -> B Y
bu' n = repeat n (mapB g . up) . mapB ex . ch 1 . map f

-- Instances of X, Y, f, and g.
{-
-- An abstract instance that typechecks but does not run.

data X
data Y

f :: X -> Y
f = undefined

g :: L Y -> Y
g = undefined
-}

-- An instance used for testing. It simply returns the list,
-- provided that the correct sublists are generated.

type X = Char
type Y = String

f :: X -> Y
f x = [x]

g :: L Y -> Y
g xss = if subs xs == xss then xs
            else error (show xss ++ " cannot be folded back to " ++ show xs)
  where xs = head (head xss) : last xss
