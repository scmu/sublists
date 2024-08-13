-- Algorithms and Their Specifications

module Algorithm where

open import Data.Nat
open import Data.Nat.Properties 
     using (0<1+n; n<1+n; <-irrefl; ≤-refl; ≤∧≢⇒<)
open import Data.Vec
open import Data.Empty
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq 
     using (refl; _≡_)

open import Agda.Builtin.Equality
open import Relation.Nullary

open import Types
open import NatProperties 


-- just some change of names for readability

0<1+k : ∀ {k} → 0 < suc k
0<1+k = 0<1+n 

0<2+k : ∀ {k} → 0 < suc (suc k)
0<2+k = 0<1+n

-- the "upgrade" function

up : ∀ {a k n} → (0 < k) → (k < n) → B a k n → B (Vec a (suc k)) (suc k) n
up 0<0 _      (T0 _)       = ⊥-elim (<-irrefl refl 0<0)
up _  1+n<1+n (Tn _)       = ⊥-elim (<-irrefl refl 1+n<1+n)
up _  2+n<2+n (N (Tn _) _) = ⊥-elim (<-irrefl refl 2+n<2+n)
up _ _ (N (T0 p) (Tn q))     = Tn (p ∷ q ∷ [])
up _ _ (N t@(N _ _) (Tn q) ) = Tn (snoc (unTn (up 0<1+k (n<1+n _) t)) q)
up _ _ (N (T0 p) u@(N _ u')) =  
   N (mapB (λ q → p ∷ q ∷ []) u) (up ≤-refl (s≤s (bounded u')) u)
up _ 2+k<2+n (N t@(N _ _) u@(N _ u')) = 
   N (zipBW snoc (up 0<1+k (s≤s⁻¹ 2+k<2+n) t) u) 
     (up 0<2+k (s≤s (bounded u')) u)  

subs : {k : ℕ} {a : Set} → Vec a (suc k) → Vec (Vec a k) (suc k)
subs         (x ∷ [])         = [ [] ]
subs {suc k} (x ∷ xs@(_ ∷ _)) = snoc (mapL (x ∷_) (subs xs)) xs 

ch : {a : Set} {n : ℕ} → (k : ℕ) → k ≤ n → Vec a n → B (Vec a k) k n
ch zero _ _ = T0 []
ch {_} {suc n} (suc k) 1+k≤1+n (x ∷ xs) with k ≟ n
... | yes refl = Tn (x ∷ xs)
... | no k≠n = N (mapB (x ∷_) (ch k (s≤s⁻¹ 1+k≤1+n) xs)) 
                  (ch (suc k) (≤∧≢⇒< (s≤s⁻¹ 1+k≤1+n) k≠n) xs) 

-- The Top-Down Algorithm

ex : {a : Set} → Vec a 1 → a 
ex (x ∷ []) = x 

postulate
  X : Set 
  Y : Set
  f : X → Y
  g : {n : ℕ} → Vec Y (suc n) → Y

td : (n : ℕ) → (xs : Vec X (suc n)) → Y
td zero    xs = f (ex xs)  
td (suc n) xs = g (map (td n) (subs xs))

td' : (n : ℕ) → Vec Y (suc n) → Y
td' zero    xs = ex xs
td' (suc n) xs = g (map (td' n) (subs xs))

-- The Bottom-Up Algorithm


repeat : {a : Set} → (n : ℕ) → (a → a) → a → a
repeat zero    f = id
repeat (suc n) f = repeat n f ∘ f
 -- but we cannot use it directly..?