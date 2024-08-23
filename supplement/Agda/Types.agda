module Types where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Empty
open import Relation.Binary.PropositionalEquality 
    using (refl; _≡_; sym)

open import NatProperties 

data B (a : Set) : ℕ → ℕ → Set where
  T0 : ∀ {n} → a → B a 0 n
  Tn : ∀ {n} → a → B a (suc n) (suc n)
  N  : ∀ {k n} → B a k n → B a (suc k) n → B a (suc k) (suc n) 

bounded : {a : Set} → {k n : ℕ} → B a k n → k ≤ n 
bounded (T0  x) = z≤n
bounded (Tn  x) = s≤s ≤-refl
bounded (N t u) = s≤s (bounded t)

snoc : {a : Set} → {n : ℕ} → Vec a n → a → Vec a (suc n)
snoc []       z = [ z ]
snoc (x ∷ xs) z = x ∷ snoc xs z

-- B a k n → k ≤ n
invalidU : ∀ {a n} → B a (suc n) n → ⊥
invalidU (N t u) = invalidU t 

unTn : {a : Set} → {n : ℕ} → B a (suc n) (suc n) → a
unTn (Tn x)  = x 
unTn (N t u) = ⊥-elim (invalidU u)

mapB : {a b : Set} → {k n : ℕ} → (a → b) → B a k n → B b k n
mapB f (T0  x) = T0 (f x)
mapB f (Tn  x) = Tn (f x)
mapB f (N t u) = N (mapB f t) (mapB f u)

zipBW : {a b c : Set} {k n : ℕ} → (a → b → c) → B a k n → B b k n → B c k n
zipBW f (T0 x)    (T0 y)    = T0 (f x y)
zipBW f (Tn x)    (Tn y)    = Tn (f x y)
zipBW f (N t1 u1) (N t2 u2) = N (zipBW f t1 t2) (zipBW f u1 u2)
zipBW f (Tn x) (N t u) = ⊥-elim (invalidU u)
zipBW f (N t u) (Tn x) = ⊥-elim (invalidU u)
