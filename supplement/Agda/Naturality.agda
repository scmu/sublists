-- Algorithms and Their Specifications

module Naturality where

open import Data.Nat
open import Data.Nat.Properties 
     using (<-irrefl; ≤-reflexive; ≤-irrelevant)
open import Data.Vec
open import Data.Empty
open import Relation.Binary.PropositionalEquality 
     using (refl; _≡_; sym)

open import Agda.Builtin.Equality
open import Relation.Nullary

open import Types
open import Algorithm
open import Properties
open import NatProperties


snoc-natural : {a b : Set} {n : ℕ}
    → (f : a → b) (xs : Vec a n) (z : a)
    → map f (snoc xs z) ≡ snoc (map f xs) (f z) 
snoc-natural f [] z = refl
snoc-natural f (x ∷ xs) z rewrite snoc-natural f xs z = refl

unTn-natural : {a b : Set} {n : ℕ} 
    → (f : a → b) (t : B a (suc n) (suc n))
    → f (unTn t) ≡ unTn (mapB f t) 
unTn-natural f (Tn x) = refl
unTn-natural f (N _ u) = ⊥-elim (invalidU u) 
    
zipBW-natural : {a b c d e s : Set} {i n : ℕ}
  → (h : a → b) (f : c → d → a) 
  → (k : e → s → b) (g : c → e) (r : d → s) 
  → (∀ x y → h (f x y) ≡ k (g x) (r y))
  → (t : B c i n) (u : B d i n)
  → mapB h (zipBW f t u) ≡ zipBW k (mapB g t) (mapB r u)
zipBW-natural h f k g r dist (T0 x) (T0 y) rewrite dist x y = refl
zipBW-natural h f k g r dist (Tn x) (Tn y) rewrite dist x y = refl
zipBW-natural h f k g r dist (Tn _) (N _ u) = ⊥-elim (invalidU u)
zipBW-natural h f k g r dist (N _ t) (Tn _) = ⊥-elim (invalidU t)
zipBW-natural h f k g r dist (N t₀ t₁) (N u₀ u₁) 
 rewrite zipBW-natural h f k g r dist t₀ u₀
       | zipBW-natural h f k g r dist t₁ u₁
 = refl

up-natural : {a b : Set}  {n k : ℕ} 
   → (f : a → b)
   → (0<k : 0 < k) → (k<n : k < n)
   → (t : B a k n) 
   → up 0<k k<n (mapB f t) ≡ mapB (map f) (up 0<k k<n t)

up-natural f _ 1+n<1+n (Tn _) = ⊥-elim (<-irrefl refl 1+n<1+n)

up-natural f p q (N t u) with t in eqt
... | Tn _ = ⊥-elim (<-irrefl refl q)
... | T0 x 
    with u in equ
...   | Tn _ = refl
...   | N u₀ u₁ 
  rewrite sym (mapB-compose (λ q₁ → f x ∷ q₁ ∷ []) f (N u₀ u₁))
        | sym (mapB-compose (map f) (λ q₁ → x ∷ q₁ ∷ []) (N u₀ u₁))
        | ≤-irrelevant (s≤s (bounded (mapB f u₁))) (s≤s (bounded u₁))
  with up-natural f (s≤s z≤n) (s≤s (bounded u₁)) u
... | ind rewrite equ
  rewrite ind
   = refl

up-natural f p q (N t u) | N t₀ t₁ with u in equ
... | Tn x
 with up-natural f (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl))) t
... | ind
 rewrite eqt
 rewrite ind
 rewrite snoc-natural f (unTn (up (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl))) (N t₀ t₁))) x
 rewrite unTn-natural (map f) (up (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl))) (N t₀ t₁))
    = refl

up-natural f p q (N t u) | N t₀ t₁ | N u₀ u₁ 
  with up-natural f (s≤s z≤n) (s≤s⁻¹ q) t
... | indt  
  rewrite eqt 
  rewrite indt
  rewrite zipBW-natural (map f) snoc snoc (map f) f (snoc-natural f) 
            (up (s≤s z≤n) (s≤s⁻¹ q) (N t₀ t₁)) (N u₀ u₁)
  with up-natural f (s≤s z≤n) (s≤s (bounded (mapB f u₁))) u
... | indu 
  rewrite equ
  rewrite indu
  rewrite ≤-irrelevant (s≤s (bounded (mapB f u₁))) (s≤s (bounded u₁))
 = refl 