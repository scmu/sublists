module Theorems where

open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec
open import Data.Empty
open import Relation.Nullary
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
   using (refl; _≡_; _≢_; cong; sym)
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit 
open import Agda.Builtin.Sigma

open import Types
open import NatProperties 
open import Algorithm
open import Properties
open import Naturality


-- Lemmas 

ch-all-Tn : {a : Set} (n : ℕ) → (p : suc n ≤ suc n) → (xs : Vec a (suc n)) 
               → ch (suc n) p xs ≡ Tn xs
ch-all-Tn {a} zero (s≤s p) (x ∷ []) = refl
ch-all-Tn {a} (suc n) (s≤s p) (x ∷ y ∷ ys) with suc n ≟ suc n 
... | yes refl   = refl
... | no 1+n≠1+n = ⊥-elim (1+n≠1+n refl)

subs-single : {a : Set} {z : a} 
   → (xs : Vec a 1) → (λ x → (z ∷ []) ∷ x ∷ []) xs ≡ (λ xs → subs (z ∷ xs)) xs
subs-single (x ∷ []) = refl

zip-snoc-subs : {a : Set} {m n k : ℕ} 
   → (z : a) (u : B (Vec a (suc m)) n k)
   → zipBW snoc (mapB (mapL (z ∷_)) (mapB subs u)) u ≡
      mapB subs (mapB (z ∷_) u)
zip-snoc-subs z (T0 (x ∷ xs)) = refl
zip-snoc-subs z (Tn (x ∷ xs)) = refl
zip-snoc-subs z (N t u) 
  rewrite zip-snoc-subs z t | zip-snoc-subs z u = refl

-- Theorem 1

thm1 : {k n : ℕ} {a : Set} → (p : 0 < k) → (q : k < n) 
     → (xs : Vec a n) 
     → up p q (ch k (<⇒≤ q) xs) ≡ mapB subs (ch (suc k) q xs) 
thm1 {suc k} {.1} _ (s≤s ()) (x ∷ [])

thm1 {suc zero} {.(2+ zero)} _ _ (x ∷ y ∷ []) = refl

thm1 {2+ k} {.(2+ zero)} _ (s≤s (s≤s ())) (x ∷ y ∷ [])

thm1 {k} {2+ (suc n)} _ 3+≤3+ (x ∷ xs) with k ≟ 2+ n
... | yes refl with suc n ≟ 2+ n 
... | yes ()
... | no 1+≠2+ with 3+≤3+
... | s≤s (s≤s (s≤s n≤n)) 
 rewrite ch-all-Tn (suc n) (s≤s (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) (λ x₁ → 1+≠2+ (cong suc x₁)))) xs
 with thm1 {suc n} {2+ n} (s≤s z≤n) (s≤s (≤-reflexive refl)) xs
... | ind
 with xs 
... | y ∷ ys 
 with suc n ≟ suc n | n ≟ suc n
... | no neg | _ = ⊥-elim (neg refl)
... | yes refl | yes ()
... | yes refl | no n≠1+n
 rewrite up-natural (x ∷_) (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl)))
           (N (mapB (y ∷_) (ch n (<⇒≤ (s≤s n≤n)) ys))
              (ch (suc n) (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) n≠1+n) ys))
 rewrite ≤-irrelevant (<⇒≤ (s≤s (≤-reflexive refl))) (<⇒≤ (s≤s n≤n))
 rewrite ind
 = refl

thm1 {suc zero} {2+ (suc n)} _ 2≤3+ (x ∷ xs) | no 1≠2+n 
 with thm1 {1} (s≤s z≤n) (s≤s (s≤s z≤n)) xs 
... | ind with xs
... | y ∷ ys 
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ (<⇒≤ 2≤3+)) (≡⇒≡ᵇ 0 (2+ n))) (s≤s z≤n) 
 rewrite ≤-irrelevant (s≤s (bounded (ch 1 (s≤s z≤n) ys))) (s≤s (s≤s z≤n)) 
 rewrite ind
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ 2≤3+) 1≠2+n) (s≤s (s≤s z≤n))
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ (s≤s⁻¹ 2≤3+)) (≡⇒≡ᵇ 0 (suc n))) (s≤s z≤n)
 rewrite sym (mapB-compose subs (x ∷_) (ch 1 (s≤s z≤n) ys))
 rewrite mapB-cong (λ q₁ → (x ∷ []) ∷ q₁ ∷ []) (λ x₁ → subs (x ∷ x₁)) 
            subs-single (ch 1 (s≤s z≤n) ys)
 = refl

thm1 {2+ k} {2+ (suc n)} 1≤2+k 3+k≤3+n (x ∷ xs) | no 2+k≠2+n with suc k ≟ 2+ n
... | yes refl = ⊥-elim (<-irrefl refl 3+k≤3+n) 
... | no 1+k≠2+n
 with ch-non-single k (s≤s⁻¹ (<⇒≤ 3+k≤3+n)) xs 1+k≠2+n 
    | ch-non-single (suc k) (≤∧≢⇒< (s≤s⁻¹ (<⇒≤ 3+k≤3+n)) 1+k≠2+n) xs 2+k≠2+n 
... | (t₀ , t₁ , ch₀) | (u₀ , u₁ , ch₁)
  -- ch₀ : ch (suc k) xs ≡ N t₀ t₁ 
  -- ch₁ : ch (2+  k) xs ≡ N u₀ u₁
 rewrite ch₀ | ch₁
 rewrite up-natural (x ∷_) (s≤s z≤n) (s≤s⁻¹ 3+k≤3+n) (N t₀ t₁)
 rewrite sym ch₀
 with thm1 (s≤s z≤n) (s≤s⁻¹ 3+k≤3+n) xs
... | ind
 rewrite ≤-irrelevant (s≤s⁻¹ (<⇒≤ 3+k≤3+n)) (<⇒≤ (s≤s⁻¹ 3+k≤3+n))
 rewrite ind
 rewrite sym ch₁ 
 rewrite ≤-irrelevant (≤∧≢⇒< (<⇒≤ (s≤s⁻¹ 3+k≤3+n)) 1+k≠2+n) (s≤s⁻¹ 3+k≤3+n)
 rewrite zip-snoc-subs x (ch (2+ k) (s≤s⁻¹ 3+k≤3+n) xs)
 rewrite ≤-irrelevant (s≤s⁻¹ 3+k≤3+n) (<⇒≤ (s≤s (bounded u₁)))
 rewrite thm1 (s≤s z≤n) (s≤s (bounded u₁)) xs
 rewrite ≤-irrelevant (≤∧≢⇒< (<⇒≤ (s≤s (bounded u₁))) 2+k≠2+n) (s≤s (bounded u₁))
 = refl
