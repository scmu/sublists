module NatProperties where

open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
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

1+n≡n+1 : ∀{n} → 1 + n ≡ n + 1
1+n≡n+1 {n = zero} = refl
1+n≡n+1 {n = suc n} = cong suc 1+n≡n+1

-- 1+k < 1+n → 1+k ≠ n → k < n

-- lemma3 : {n k : ℕ} → (suc k ≤ suc n) → (¬ suc k ≡ suc n) → (suc k ≤ n)
-- lemma3 p q = ≤-pred (≤∧≢⇒< p q)