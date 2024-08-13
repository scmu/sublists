-- Properties Regarding Our Algorithmic Components
module Properties where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties 
     using (≤∧≢⇒<)
open import Data.Vec
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
     using (refl; _≡_; _≢_; sym; cong₂)

open import Agda.Builtin.Equality
open import Relation.Nullary

open import Types
open import Algorithm 

-- mapB composition and congruence

mapB-compose : ∀ {n k} {a : Set} {b : Set} {c : Set} 
               (f : b → c) (g : a → b) (t : B a n k) →
               mapB (f ∘ g) t ≡ mapB f (mapB g t)
mapB-compose f g (T0 x)  = refl
mapB-compose f g (Tn x)  = refl
mapB-compose f g (N t u) = cong₂ N ((mapB-compose f g t)) ((mapB-compose f g u))

mapB-cong : ∀ {a b} (f g : a → b) 
          → (∀ x → f x ≡ g x) 
          → ∀ {n k} → (t : B a n k) → mapB f t ≡ mapB g t
mapB-cong f g f≡g (T0 x) rewrite f≡g x = refl
mapB-cong f g f≡g (Tn x) rewrite f≡g x = refl
mapB-cong f g f≡g (N t u) 
  rewrite mapB-cong f g f≡g t 
  rewrite mapB-cong f g f≡g u = refl

-- ch : {a : Set} {n : ℕ} → (k : ℕ) → k ≤ n → Vec a n → B (Vec a k) k n

ch-non-single : {a : Set} {n : ℕ} 
    → (k : ℕ) → (1+k≤1+n : suc k ≤ suc n) → (xs : Vec a (suc n))
    → suc k ≢ suc n 
    → Σ[ t ∈ B (Vec a (suc k)) k n ] 
      Σ[ u ∈ B (Vec a (suc k)) (suc k) n ]
          (ch (suc k) 1+k≤1+n xs ≡ N t u)
ch-non-single {n = n} k 1+k≤1+n (x ∷ xs) k≠n with k ≟ n
... | yes refl = ⊥-elim (k≠n refl) 
... | no k≠n = ( mapB (_∷_ x) (ch k (s≤s⁻¹ 1+k≤1+n) xs) 
               , ch (suc k) (≤∧≢⇒< (s≤s⁻¹ 1+k≤1+n) k≠n) xs
               , refl)