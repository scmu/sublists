-- Algorithms and Their Specifications

module Naturality where

open import Data.Nat
open import Data.Nat.Properties 
     using (0<1+n; n<1+n; <-irrefl; ≤-refl; ≤∧≢⇒<)
open import Data.Vec
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq 
     using (refl; _≡_; cong; sym; subst)
open Eq.≡-Reasoning

open import Agda.Builtin.Equality
open import Relation.Nullary

open import Types
open import Algorithm


-- up : ∀ {a k n} → (0 < k) → (k < n) → B a k n → B (Vec a (suc k)) (suc k) n

postulate

 up-natural : {n k : ℕ} {a b : Set} 
   → (f : a → b)
   → (0<k : 0 < k) → (k<n : k < n)
   → (t : B a k n) 
   → up 0<k k<n (mapB f t) ≡ mapB (mapL f) (up 0<k k<n t)
