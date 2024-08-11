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


lemma-ch-eq-Tn : {a : Set} (n : ℕ) → (p : suc n ≤ suc n) → (xs : Vec a (suc n)) 
               → ch (suc n) p xs ≡ Tn xs
lemma-ch-eq-Tn {a} zero (s≤s p) (x ∷ []) = refl
lemma-ch-eq-Tn {a} (suc n) (s≤s p) (x ∷ y ∷ ys) with suc n ≟ suc n 
... | yes refl   = refl
... | no 1+n≠1+n = ⊥-elim (1+n≠1+n refl)


postulate
  funext : ∀ {a b : Set} {f g : a → b} → (∀ x → f x ≡ g x) → f ≡ g
  h3 : ∀ {n k} → suc k ≤ suc (suc (suc n)) → 1 ≤ k → ¬ k ≡ 1 → ¬ suc k ≡ suc (suc (suc n)) → ⊥ 

h1 : ∀ {k n} → suc k ≤ n → n ≤ k → ⊥ 
h1 = <⇒≱

h2 : ∀ {k} → suc k ≤ 2 → 1 ≤ k → ¬ k ≡ 1 → ⊥ 
h2 {suc zero} p q r = r refl
h2 {2+ k} (s≤s (s≤s ())) q r

-- case 2
ssn≠sssn : {n : ℕ} → suc (suc n) ≡ suc (suc (suc n)) → ⊥
ssn≠sssn ()

sn≠ssn : {n : ℕ} →  suc n ≡ suc (suc n) → ⊥
sn≠ssn ()

q≡sn≢n : ∀ {n}  (q : ¬ suc n ≡ suc (suc n)) → (sn≢n : ¬ suc n ≡ suc (suc n)) → q ≡ sn≢n
q≡sn≢n = λ q sn≢n → funext (λ x → ⊥-elim (sn≢n x))

thm1 : {k n : ℕ} {a : Set} → (p : 0 < k) → (q : k < n) 
     -- → (r1 : k ≤ n) -- → (r2 : suc k ≤ n) 
     → (xs : Vec a n) 
     → up p q (ch k (<⇒≤ q) xs) ≡ mapB subs (ch (suc k) q xs) 
thm1 {k} {n} p q xs with suc k ≟ n | k ≟ 1 
thm1 {.1} {.2} _ (s≤s (s≤s z≤n)) (y ∷ z ∷ []) | yes refl | yes refl = refl 
thm1 {.1} {.2} 1≤1 2≤2 (y ∷ z ∷ []) | yes refl | no 1≠1 = ⊥-elim (1≠1 refl)

thm1 {_} {2+ (suc n)} p (s≤s (s≤s 1+n≤1+n)) (x ∷ xs) | yes refl | no 2+n≠1 
  with suc n ≟ 2+ n | 2+ n ≟ 2+ n 
... | yes () | _
... | no _ | no neq = ⊥-elim (neq refl)
... | no 1+n≠2+n | yes refl 
  rewrite lemma-ch-eq-Tn (suc n) ((≤∧≢⇒< (<⇒≤ (s≤s 1+n≤1+n)) 1+n≠2+n)) xs 
  with thm1 {suc n} {2+ n} (s≤s z≤n) (s≤s (≤-reflexive refl)) xs
... | ind with suc n ≟ suc n
... | no neq = ⊥-elim (neq refl)
... | yes _  with xs
... | y ∷ ys with suc n ≟ suc n | n ≟ suc n
...   | no neq | _ = ⊥-elim (neq refl)
...   | yes refl | yes ()
...   | yes refl | no n≠1+n with 1+n≤1+n
...    | s≤s n≤n with n ≟ suc n
...    | yes ()  
...    | no n≠1+n' rewrite up-natural (x ∷_) (s≤s z≤n) (s≤s (s≤s (≤-reflexive refl))) 
                            (N (mapB (_∷_ y) (ch n (<⇒≤ (s≤s n≤n)) ys))
                               (ch (suc n) (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) n≠1+n') ys))
                   rewrite ≤-irrelevant (≤∧≢⇒< (<⇒≤ (s≤s (≤-reflexive refl))) n≠1+n)
                                        (≤∧≢⇒< (<⇒≤ (s≤s n≤n)) n≠1+n')
                   rewrite ≤-irrelevant (s≤s n≤n) (≤-reflexive refl)
                   rewrite ind
         = refl

thm1 {.1} {.1} _ (s≤s ()) (x ∷ []) | no _ | yes refl

thm1 {.1} {.(2+ _)} p q (x ∷ x₁ ∷ xs) | no r | yes refl = {!   !} 

thm1 {k} {n} p q xs | no r | no r2 = {!   !} 

 