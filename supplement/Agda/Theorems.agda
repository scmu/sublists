module Theorems where

open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec
open import Data.Empty
open import Agda.Builtin.Equality
open import Relation.Nullary
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; sym; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; step-≡; _∎)
open Eq.≡-Reasoning
open import Relation.Nullary.Reflects 
open import Data.Bool.Properties using (T?)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit 

open import Types
open import NatProperties 
open import Algorithm
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

-- Theorem 1

thm1 : {k n : ℕ} {a : Set} → (p : 0 < k) → (q : k < n) 
     → (xs : Vec a n) 
     → up p q (ch k (<⇒≤ q) xs) ≡ mapB subs (ch (suc k) q xs) 
thm1 {suc k} {.1} _ (s≤s ()) (x ∷ [])

thm1 {suc zero} {.(2+ zero)} p q (x ∷ y ∷ []) = refl

thm1 {2+ k} {.(2+ zero)} p (s≤s (s≤s ())) (x ∷ y ∷ [])

thm1 {k} {2+ (suc n)} p 3+≤3+ (x ∷ xs) with k ≟ 2+ n
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

thm1 {suc zero} {2+ (suc n)} p q (x ∷ xs) | no 1≠2+n 
 with thm1 {1} (s≤s z≤n) (s≤s (s≤s z≤n)) xs 
... | ind with xs
... | y ∷ ys 
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ (<⇒≤ q)) (≡⇒≡ᵇ 0 (2+ n))) (s≤s z≤n) 
 rewrite ≤-irrelevant (s≤s (bounded (ch 1 (s≤s z≤n) ys))) (s≤s (s≤s z≤n)) 
 rewrite ind
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ q) 1≠2+n) (s≤s (s≤s z≤n))
 rewrite ≤-irrelevant (≤∧≢⇒< (s≤s⁻¹ (s≤s⁻¹ q)) (≡⇒≡ᵇ 0 (suc n))) (s≤s z≤n)
 rewrite sym (mapB-compose subs (x ∷_) (ch 1 (s≤s z≤n) ys))
 rewrite mapB-cong (λ q₁ → (x ∷ []) ∷ q₁ ∷ []) (λ x₁ → subs (x ∷ x₁)) 
            subs-single (ch 1 (s≤s z≤n) ys)
 = refl

thm1 {2+ k} {2+ (suc n)} p q (x ∷ xs) | no 2+k≠2+n = {!   !} 

{-
thm1 {k} {n} p q xs with suc k ≟ n | k ≟ 1 
thm1 {.1} {.2} _ (s≤s (s≤s z≤n)) (y ∷ z ∷ []) | yes refl | yes refl = refl 
thm1 {.1} {.2} 1≤1 2≤2 (y ∷ z ∷ []) | yes refl | no 1≠1 = ⊥-elim (1≠1 refl)

thm1 {_} {2+ (suc n)} p (s≤s (s≤s (s≤s n≤n))) (x ∷ xs) | yes refl | no 2+n≠1 
 with suc n ≟ 2+ n | 2+ n ≟ 2+ n 
... | yes () | _ 
... | no _ | no neq = ⊥-elim (neq refl)
... | no 1+n≠2+n | yes refl 
 rewrite ch-all-Tn (suc n) (s≤s (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) (λ x₁ → 1+n≠2+n (cong suc x₁)))) xs
 with thm1 {suc n} {2+ n} (s≤s z≤n) (s≤s (≤-reflexive refl)) xs
... | ind
 with xs 
... | y ∷ ys 
 with suc n ≟ suc n | n ≟ suc n 
... | no neg | _ = ⊥-elim (neg refl)
... | yes refl | yes () 
... | yes refl | no n≠1+n 
 rewrite up-natural (x ∷_) (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl))) 
                             (N (mapB (_∷_ y) (ch n (<⇒≤ (s≤s n≤n)) ys))
                                (ch (suc n) (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) n≠1+n) ys))
 rewrite ≤-irrelevant (<⇒≤ (s≤s (≤-reflexive refl))) (<⇒≤ (s≤s n≤n))
 rewrite ind
 = refl

thm1 {.1} {.1} _ (s≤s ()) (x ∷ [])    | no _ | yes refl

thm1 {.1} {2} p (s≤s (s≤s z≤n)) (x ∷ x₁ ∷ xs) | no neg  | yes refl = ⊥-elim (neg refl)

thm1 {suc k} {2+ (suc n)} 1≤1 (s≤s (s≤s z≤n)) (x ∷ xs@(y ∷ ys@(z ∷ zs))) | no 2≠2+n | yes refl 
  with 1 ≟ suc n
... | yes refl  with zs 
... | [] = refl
thm1 {suc k} {2+ (suc n)} 1≤1 (s≤s (s≤s z≤n)) (x ∷ xs@(y ∷ ys@(z ∷ zs))) | no 2≠2+n | yes refl  | no neg 
  = {!   !}

thm1 {k} {n} p q xs | no r | no r2 = {!   !} 
  
-}