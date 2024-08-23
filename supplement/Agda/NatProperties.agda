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

1+m≤n⇒m≤n : ∀ {m n} → 1 + m ≤ n → m ≤ n
1+m≤n⇒m≤n {zero} {n} _ = z≤n
1+m≤n⇒m≤n {suc m} {.(suc _)} (s≤s 1+m≤n) = s≤s (1+m≤n⇒m≤n 1+m≤n)
