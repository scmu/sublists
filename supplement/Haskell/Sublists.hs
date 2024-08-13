type Nat = Int
type L a = [a]

subs :: L a -> L (L a)
subs []      = []
subs (x:xs)  = map (x:) (subs xs) ++ [xs] {-"~~."-}

choose :: Nat -> L a -> L (L a)
choose 0  _       =  [[]]
choose k  xs      |  k == length xs = [xs]
choose k  (x:xs)  =  map (x:) (choose (k-1) xs) ++ choose k xs

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

up :: B a -> B (L a)
up (N (T p)  (T q)  ) = T [p,q]
up (N t      (T q)  ) = T (unT (up t) ++ [q])
up (N (T p)  u      ) = N (mapB (\q -> [p,q]) u) (up u)
up (N t      u      ) = N (zipBW snoc (up t) u) (up u)
