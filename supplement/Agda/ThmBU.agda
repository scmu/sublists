module ThmBU where

open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec
open import Data.Empty
open import Relation.Nullary
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
   using (refl; _≡_; _≢_; cong; sym)
open import Relation.Binary.HeterogeneousEquality 
   using (_≅_; ≡-to-≅ )
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit 
open import Agda.Builtin.Sigma

open import Types
open import NatProperties 
open import Algorithm
open import Properties
open import Naturality
open import ThmUpgrade

td-td' : ∀ n → (xs : Vec X (suc n))
  → td n xs ≡ td' n (map f xs)
td-td' zero (x ∷ []) = refl
td-td' (suc n) (x ∷ xs) 
  rewrite sym (subs-natural f (x ∷ xs)) 
  rewrite sym (map-compose (td' n) (map f) (subs (x ∷ xs)))
  rewrite map-cong (td n) (td' n ∘ map f) (td-td' n) (subs (x ∷ xs))
  = refl

mapB-td'-expand : ∀ {n k m} 
  → (t : B (Vec Y (2 + n)) k m)
  → mapB (td' (1 + n)) t ≡ 
      mapB g (mapB (map (td' n)) (mapB subs t))
mapB-td'-expand (T0 _) = refl
mapB-td'-expand (Tn _) = refl
mapB-td'-expand {n} (N t u) 
   rewrite mapB-compose g (λ xs → map (td' n) (subs xs)) t 
         | mapB-compose g (λ xs → map (td' n) (subs xs)) u 
   rewrite mapB-compose (map (td' n)) subs t 
         | mapB-compose (map (td' n)) subs u = refl

td'-repeatUp : {n m : ℕ}  
  → (n<m : n < m) → (0<m : 0 < m) 
  → (xs : Vec Y m)
  → (mapB (td' n) ∘ ch (1 + n) n<m) xs ≡ 
      (repeatUp n n<m ∘ mapB ex ∘ ch 1 0<m) xs
td'-repeatUp {zero} 0<m' 0<m xs rewrite ≤-irrelevant 0<m' 0<m = refl
td'-repeatUp {suc n} 1+n<m 0<m xs 
 rewrite mapB-td'-expand (ch (2 + n) 1+n<m xs)
 rewrite sym (up-ch (s≤s z≤n) 1+n<m xs)
 rewrite sym (up-natural (td' n) (s≤s z≤n) 1+n<m (ch (suc n) (<⇒≤ 1+n<m) xs))
 rewrite td'-repeatUp (<⇒≤ 1+n<m) 0<m xs
 rewrite ≤-irrelevant (1+m≤n⇒m≤n 1+n<m) (<⇒≤ 1+n<m)
 = refl

td-bu : ∀ {n} → (xs : Vec X (suc n))
      → td n xs ≡ bu n xs
td-bu {zero} (x ∷ []) = refl
td-bu {suc n} xs 
 rewrite td-td' (suc n) xs 
 rewrite cong subs (sym (ch-all-id ≤-refl (map f xs)))
 rewrite unTn-natural (td' (1 + n)) (ch (2 + n) ≤-refl (map f xs))
 rewrite td'-repeatUp ≤-refl (s≤s z≤n) (map f xs)
 = refl