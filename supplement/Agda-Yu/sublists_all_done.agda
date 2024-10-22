open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties 
open import Data.Vec
open import Data.Empty
open import Agda.Builtin.Equality
open import Relation.Nullary
open import Function using (_∘_; id; _$_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; sym; subst; _≢_)
open Eq.≡-Reasoning -- using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary.Reflects 
open import Data.Bool.Properties using (T?)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit 
open import Agda.Builtin.Sigma

import Relation.Binary.HeterogeneousEquality as HEq 

data B (a : Set) : ℕ → ℕ → Set where
  T0 : ∀ {n} → a → B a 0 n
  Tn : ∀ {n} → a → B a (suc n) (suc n)
  N  : ∀ {k n} → B a k n → B a (suc k) n → B a (suc k) (suc n) 

-- 1 + n ≡ suc n
1+n≡n+1 : ∀{n} → 1 + n ≡ n + 1
1+n≡n+1 {n = zero} = refl
1+n≡n+1 {n = suc n} = cong suc 1+n≡n+1

-- old snoc, but is harder for agda to refine
-- snoc : {a : Set} → {n : ℕ} → Vec a n → a → Vec a (suc n)
-- snoc [] x = [ x ]
-- snoc {a} {suc k} (x ∷ xs) y rewrite cong suc (1+n≡n+1 {k}) = (x ∷ xs) ++ [ y ]

snoc : {a : Set} → {n : ℕ} → Vec a n → a → Vec a (suc n)
snoc []       z = [ z ]
snoc (x ∷ xs) z = x ∷ snoc xs z

cannotBeConstructedByN : ∀ {a k n} → B a (suc k) (suc n) → Set
cannotBeConstructedByN (N _ _) = ⊥ -- bottom type, indicating an impossible case
cannotBeConstructedByN _       = ⊤ -- true for other constructors

-- B a k n → k ≤ n
invalidU : ∀ {a n} → B a (suc n) n → ⊥
invalidU (N t u) = invalidU t

-- B a (suc n) (suc n) must be N _ _ 
lemma1 : ∀ {a n} → (b : B a (suc n) (suc n)) → cannotBeConstructedByN b
lemma1 (Tn _) = tt -- true for Tn constructor
lemma1 (N t u) = (invalidU u)

unTn : {a : Set} → {n : ℕ} → B a (suc n) (suc n) → a
unTn (Tn x) = x 
unTn (N t u) = ⊥-elim (lemma1 (N t u)) 

mapB : {a b : Set} → {k n : ℕ} → (a → b) → B a k n → B b k n
mapB f (T0 x)= T0 (f x)
mapB f (Tn x)= Tn (f x)
mapB f (N t u)= N (mapB f t) (mapB f u)

bounded : {a : Set } → {k n : ℕ} → B a k n → k ≤ n 
bounded (T0 x) = z≤n
bounded (Tn x) = ≤-refl
bounded (N t u) = s≤s (bounded t)


zipBW : {a b c : Set} {k n : ℕ} → (a → b → c) → B a k n → B b k n → B c k n
zipBW f (T0 x) (T0 y) = T0 (f x y)
zipBW f (Tn x) (Tn y) = Tn (f x y)
zipBW f (N t1 u1) (N t2 u2) = N (zipBW f t1 t2) (zipBW f u1 u2)
zipBW f (Tn x) (N t u) = ⊥-elim (invalidU u)
zipBW f (N t u) (Tn x) = ⊥-elim (invalidU u)

up : ∀ {a k n} → (0 < k) → (k < n) → B a k n → B (Vec a (suc k)) (suc k) n
up 0<0 _ (T0 x) = ⊥-elim (<-irrefl refl 0<0)
up _  1+n<1+n (Tn x) =  ⊥-elim (<-irrefl refl 1+n<1+n)
up _  2+n<2+n (N (Tn _) _) = ⊥-elim (<-irrefl refl 2+n<2+n)
up _ _ (N (T0 p) (Tn q)) = Tn (p ∷ q ∷ [])
up _ _ (N t@(N _ _) (Tn q) ) = Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) t)) q)
up _ _ (N (T0 p) u@(N _ u')) = N (mapB (λ q → p ∷ q ∷ []) u) (up ≤-refl (s≤s (bounded u')) u)
up _ (s≤s 1+k<1+n) (N t@(N _ _) u@(N _ u')) = N (zipBW snoc (up (s≤s z≤n) 1+k<1+n t) u) (up (s≤s z≤n) (s≤s (bounded u')) u)  

subs : {k : ℕ} {a : Set} → Vec a (suc k) → Vec (Vec a k) (suc k)
subs (x ∷ []) = [ [] ]
subs {suc k} (x ∷ xs@(_ ∷ _)) = snoc (map (x ∷_) (subs xs)) xs 

-- s≤s⁻¹ : ∀ {m n} → suc m ≤ suc n → m ≤ n
-- s≤s⁻¹ (s≤s m≤n) = m≤n

-- n≮0 : ∀ {n} → n ≮ 0
-- n≮0 ()

sn≰0 : ∀ {x} → suc x ≤ zero → ⊥ 
sn≰0 ()

not-suc-eq-suc : ∀ {x y} → ¬ suc x ≡ suc y → ¬ x ≡ y
not-suc-eq-suc notEq eq = notEq (cong suc eq)

lemma3 : {n k : ℕ} → (suc k ≤ suc n) → (¬ suc k ≡ suc n) → (suc k ≤ n)
lemma3 {zero} {zero} p q = ⊥-elim (q refl)
lemma3 {zero} {suc k} p q = ⊥-elim (lamma3helper1 p)
  where 
    lamma3helper1 : ∀ {x} → suc (suc x) ≤ 1 → ⊥ 
    lamma3helper1 {x} p = ⊥-elim (sn≰0 (s≤s⁻¹ p))
lemma3 {suc n} {zero} p q = s≤s z≤n
lemma3 {suc n} {suc k} p q =  s≤s (lemma3 (s≤s⁻¹ p) (not-suc-eq-suc q))


ch : {a : Set} {n : ℕ} → (k : ℕ) → (k ≤ n) → Vec a n → B (Vec a k) k n
ch zero _ _ = T0 []
ch {a} {suc n} (suc k) p (x ∷ xs) with suc k ≟ suc n
... | yes refl = Tn ((x ∷ xs))
... | no k≢sk = N (mapB (x ∷_) (ch k (s≤s⁻¹ p) xs)) (ch (suc k) (lemma3 p k≢sk) xs)


lemma-ch-eq-Tn : {a : Set} (n : ℕ) → (p : suc n ≤ suc n) → (xs : Vec a (suc n)) → ch (suc n) p xs ≡ Tn xs
lemma-ch-eq-Tn {a} zero p (x ∷ []) = refl
lemma-ch-eq-Tn {a} (suc n) p (x ∷ y ∷ ys) with suc (suc n) ≟ suc (suc n) 
... | yes refl = refl
... | no ssn≢ssn = ⊥-elim (ssn≢ssn refl)


postulate
  funext : ∀ {a b : Set} {f g : a → b} → (∀ x → f x ≡ g x) → f ≡ g

h1 : ∀ {k n} → suc k ≤ n → n ≤ k → ⊥ 
h1 {k} {n} p q =
  let
    r : suc k ≤ k
    r = ≤-trans p q
  in
    1+n≰n r

h2 : ∀ {k} → suc k ≤ 2 → 1 ≤ k → ¬ k ≡ 1 → ⊥ 
h2 {suc zero} p q r = r refl
h2 {suc (suc k)} p q r = tmp p
  where 
      tmp : ∀ {k} → suc (suc (suc k)) ≤ 2 → ⊥
      tmp (s≤s (s≤s ()))

n+1≡sucn : ∀ n → n + 1 ≡ suc n
n+1≡sucn zero = refl
n+1≡sucn (suc n) = cong suc (n+1≡sucn n)

sn≠sssn : ∀ {n} → ¬ suc n ≡ (suc (suc (suc n))) 
sn≠sssn {n} ()

ssn≠sssn : {n : ℕ} → suc (suc n) ≡ suc (suc (suc n)) → ⊥
ssn≠sssn ()

sn≠ssn : {n : ℕ} →  suc n ≡ suc (suc n) → ⊥
sn≠ssn ()
  

mapB-compose : ∀ {n k} {a b c : Set} 
               (f : b → c) (g : a → b) (t : B a n k) →
               mapB (f ∘ g) t ≡ mapB f (mapB g t)
mapB-compose f g (T0 x) = refl
mapB-compose f g (Tn x) = refl
mapB-compose f g (N t u) =  Eq.cong₂ N ((mapB-compose f g t)) ((mapB-compose f g u))

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

zipBW-natural-eq-input : {a b c e s : Set} {i n : ℕ}
  → (h : a → b) (f : c → c → a) 
  → (k : e → s → b) (g : c → e) (r : c → s) 
  → (∀ x → h (f x x) ≡ k (g x) (r x))
  → (t : B c i n) 
  → mapB h (zipBW f t t) ≡ zipBW k (mapB g t) (mapB r t)
zipBW-natural-eq-input h f k g r dist (T0 x) rewrite dist x  = refl
zipBW-natural-eq-input h f k g r dist (Tn x) rewrite dist x = refl
zipBW-natural-eq-input h f k g r dist (N t t₁) 
  rewrite zipBW-natural-eq-input h f k g r dist t
        | zipBW-natural-eq-input h f k g r dist t₁ 
  = refl  

up-natural : {a b : Set}  {n k : ℕ} 
   → (f : a → b)
   → (0<k : 0 < k) → (k<n : k < n)
   → (t : B a k n) 
   → up 0<k k<n (mapB f t) ≡ mapB (map f) (up 0<k k<n t)

up-natural {a} {b} {zero} {suc k} f 0<k k<n ()
up-natural {a} {b} {suc n} {suc .n} f 0<k k<n (Tn x) = ⊥-elim (n≮n (suc n) k<n)
up-natural {a} {b} {suc .1} {suc .0} f 0<k k<n (N (T0 x) (Tn x₁)) = refl
up-natural {a} {b} {suc .2} {suc .0} f 0<k k<n (N (T0 x) (N (T0 x₁) (Tn x₂))) = refl
up-natural {a} {b} {suc .(suc _)} {suc .0} f 0<k k<n (N (T0 x) (N (T0 x₁) t₂)) = 
  begin
    up 0<k k<n (mapB f (N (T0 x) (N (T0 x₁) t₂)))
  ≡⟨ refl ⟩
    N (mapB (λ q → f x ∷ q ∷ []) (N (mapB f (T0 x₁)) (mapB f t₂))) (up ≤-refl (s≤s (bounded (mapB f t₂))) (N (mapB f (T0 x₁)) (mapB f t₂)))
  ≡⟨ cong (λ w → N (mapB (λ q → f x ∷ q ∷ []) (N (mapB f (T0 x₁)) (mapB f t₂))) (up ≤-refl w (N (mapB f (T0 x₁)) (mapB f t₂)))) (≤-irrelevant (s≤s (bounded (mapB f t₂))) (s≤s (bounded t₂))) ⟩ -- rewrite ≤  
    N (mapB (λ q → f x ∷ q ∷ []) (N (mapB f (T0 x₁)) (mapB f t₂))) (up ≤-refl (s≤s (bounded t₂)) (N (mapB f (T0 x₁)) (mapB f t₂)))
  ≡⟨ cong (λ w → N w (up ≤-refl (s≤s (bounded t₂)) (N (mapB f (T0 x₁)) (mapB f t₂)))) (cong (λ w' → N (T0 (f x ∷ f x₁ ∷ [])) w') (sym (mapB-compose (λ q → f x ∷ q ∷ []) f t₂))) ⟩ -- mapB-compose 
    N (N (T0 (f x ∷ f x₁ ∷ [])) (mapB ((λ q → f x ∷ q ∷ []) ∘ f) t₂)) (up ≤-refl (s≤s (bounded t₂)) (N (mapB f (T0 x₁)) (mapB f t₂)))
  ≡⟨ cong(λ w → N (N (T0 (f x ∷ f x₁ ∷ [])) w) (up ≤-refl (s≤s (bounded t₂)) (N (mapB f (T0 x₁)) (mapB f t₂)))) pf1 ⟩ 
    N (mapB (map f) (N (T0 (x ∷ x₁ ∷ [])) (mapB (λ q → x ∷ q ∷ []) t₂))) (up ≤-refl (s≤s (bounded t₂)) (mapB f (N (T0 x₁) t₂)))
  ≡⟨ cong (λ w → N (mapB (map f) (N (T0 (x ∷ x₁ ∷ [])) (mapB (λ q → x ∷ q ∷ []) t₂))) w) (up-natural f ≤-refl (s≤s (bounded t₂)) (N (T0 x₁) t₂)) ⟩
    N (mapB (map f) (N (T0 (x ∷ x₁ ∷ [])) (mapB (λ q → x ∷ q ∷ []) t₂))) (mapB (map f) (up ≤-refl (s≤s (bounded t₂)) (N (T0 x₁) t₂)))
  ≡⟨ refl ⟩ -- def. of mapB
    mapB (map f) (N (N (T0 (x ∷ x₁ ∷ [])) (mapB (λ q → x ∷ q ∷ []) t₂)) (up ≤-refl (s≤s (bounded t₂)) (N (T0 x₁) t₂)))
  ≡⟨ refl ⟩ -- def. of up
    mapB (map f) (up 0<k k<n (N (T0 x) (N (T0 x₁) t₂)))
  ∎ 
  where 
    pf1 : mapB (λ x₂ → f x ∷ f x₂ ∷ []) t₂ ≡ mapB (map f) (mapB (λ q → x ∷ q ∷ []) t₂)
    pf1 = 
      begin 
        mapB (λ x₂ → f x ∷ f x₂ ∷ []) t₂
      ≡⟨ refl ⟩
        mapB (map f ∘ (λ x₂ → x ∷ x₂ ∷ [])) t₂ 
      ≡⟨ mapB-compose (map f) (λ x₂ → x ∷ x₂ ∷ []) t₂ ⟩ 
        mapB (map f) (mapB (λ q → x ∷ q ∷ []) t₂)
      ∎
up-natural {a} {b} {suc .(suc _)} {suc .(suc _)} f 0<k k<n (N (Tn x) (N t₁ t₂)) = ⊥-elim (invalidU t₁)
up-natural {a} {b} {suc .(suc (suc _))} {suc .(suc _)} f 0<k k<n (N (N t (Tn x₁)) (Tn x)) =
  begin 
    up 0<k k<n (mapB f (N (N t (Tn x₁)) (Tn x)))
  ≡⟨ refl ⟩ -- def. of up
    Tn (snoc (unTn (up (s≤s z≤n) ≤-refl (N (mapB f t) (mapB f (Tn x₁))))) (f x))
  ≡⟨ cong (λ w → Tn (snoc (unTn w) (f x))) (up-natural f (s≤s z≤n) ≤-refl (N t (Tn x₁))) ⟩ 
    Tn (snoc (unTn (mapB (map f)  (up (s≤s z≤n) ≤-refl (N t (Tn x₁))))) (f x))
  ≡⟨ cong (λ w → Tn (snoc w (f x))) (sym (unTn-natural (map f)  (up (s≤s z≤n) ≤-refl (N t (Tn x₁))))) ⟩
    Tn (snoc (map f (unTn (up (s≤s z≤n) ≤-refl (N t (Tn x₁))))) (f x))
  ≡⟨ cong Tn (sym (snoc-natural f (unTn (up (s≤s z≤n) ≤-refl (N t (Tn x₁)))) x)) ⟩ 
    Tn ((map f) (snoc (unTn (up (s≤s z≤n) ≤-refl (N t (Tn x₁)))) x))
  ≡⟨ refl ⟩ -- def. of mapB
    mapB (map f) (Tn (snoc (unTn (up (s≤s z≤n) ≤-refl (N t (Tn x₁)))) x))
  ≡⟨ refl ⟩ -- def. of up
    mapB (map f) (up 0<k k<n (N (N t (Tn x₁)) (Tn x)))
  ∎ 

up-natural {a} {b} {suc .(suc (suc _))} {suc .(suc _)} f 0<k k<n (N (N t (N t₁ t₂)) (Tn x)) = ⊥-elim (invalidU t₂)
up-natural {a} {b} {suc .(suc _)} {suc .(suc _)} f 0<k k<n (N (N t t₁) (N t₂ t₃)) =
  begin 
    up 0<k k<n (mapB f (N (N t t₁) (N t₂ t₃)))
  ≡⟨ cong (λ w → up 0<k w (mapB f (N (N t t₁) (N t₂ t₃)))) (≤-irrelevant k<n (s≤s (s≤s⁻¹ k<n))) ⟩ -- to get an s≤s... -- historical issue
    up (s≤s z≤n) (s≤s (s≤s⁻¹ k<n)) (mapB f (N (N t t₁) (N t₂ t₃)))
  ≡⟨ refl ⟩ -- def. of up
    N (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (mapB f (N t t₁))) (mapB f (N t₂ t₃))) (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N (mapB f t₂) (mapB f t₃)))
  ≡⟨ cong (λ w → N (zipBW snoc w (mapB f (N t₂ t₃))) (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N (mapB f t₂) (mapB f t₃)))) (up-natural f (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) ⟩ -- induction
    N (zipBW snoc (mapB (map f) (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁))) (mapB f (N t₂ t₃))) (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N (mapB f t₂) (mapB f t₃))) 
  ≡⟨ cong (λ w → N w (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N (mapB f t₂) (mapB f t₃)))) (sym (zipBW-natural (map f) snoc snoc (map f) f (λ x y → snoc-natural f x y) (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) ⟩  -- zipBW-natural
    N (mapB (map f) (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N (mapB f t₂) (mapB f t₃)))
  ≡⟨ cong (λ w → N (mapB (map f) (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) w) (up-natural f (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N t₂ t₃)) ⟩ -- up-natural
    N (mapB (map f) (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) (mapB (map f) (up (s≤s z≤n) (s≤s (bounded (mapB f t₃))) (N t₂ t₃)))
  ≡⟨ cong (λ w → N (mapB (map f) (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) (mapB (map f) (up (s≤s z≤n) w (N t₂ t₃)))) (≤-irrelevant (s≤s (bounded (mapB f t₃))) (s≤s (bounded t₃))) ⟩ -- rewrite ≤ 
    N (mapB (map f) (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃))) (mapB (map f) (up (s≤s z≤n) (s≤s (bounded t₃)) (N t₂ t₃)))
  ≡⟨ refl ⟩ -- def. of mapB
    mapB (map f) (N (zipBW snoc (up (s≤s z≤n) (s≤s⁻¹ k<n) (N t t₁)) (N t₂ t₃)) (up (s≤s z≤n) (s≤s (bounded t₃)) (N t₂ t₃))) 
  ≡⟨ refl ⟩ -- def. of up 
    mapB (map f) (up 0<k (s≤s (s≤s⁻¹ k<n)) (N (N t t₁) (N t₂ t₃)))
  ≡⟨ cong (λ w → mapB (map f) (up 0<k w (N (N t t₁) (N t₂ t₃)))) (≤-irrelevant ((s≤s (s≤s⁻¹ k<n))) k<n) ⟩ 
    mapB (map f) (up 0<k k<n (N (N t t₁) (N t₂ t₃)))
  ∎

q≡sn≢n : ∀ {n}  (q : ¬ suc n ≡ suc (suc n)) → (sn≢n : ¬ suc n ≡ suc (suc n)) → q ≡ sn≢n
q≡sn≢n = λ q sn≢n → funext (λ x → ⊥-elim (sn≢n x))

lemma-ch-neq-rec : ∀ {n} {a : Set} → (r1 : suc n ≤ suc (suc n)) → (sn≢n : ¬ suc n ≡ suc (suc n)) →  (x : a) → (xs : Vec a (suc n)) → ch (suc n) r1 (x ∷ xs) ≡ N (mapB (x ∷_) (ch n (s≤s⁻¹ r1) xs)) (ch (suc n) (lemma3 r1 sn≢n) xs)
lemma-ch-neq-rec {n} {a} r1 sn≢n x xs with suc n ≟ suc (suc n)
... | yes p = ⊥-elim (sn≢n p)
... | no q = 
  begin 
    N (mapB (x ∷_) (ch n (s≤s⁻¹ r1) xs)) (ch (suc n) (lemma3 r1 q) xs)
  ≡⟨ cong (λ w → N (mapB (x ∷_) (ch n (s≤s⁻¹ r1) xs)) (ch (suc n) (lemma3 r1 w) xs)) (q≡sn≢n q sn≢n) ⟩  
    N (mapB (_∷_ x) (ch n (s≤s⁻¹ r1) xs)) (ch (suc n) (lemma3 r1 sn≢n) xs)
  ∎


-- case 3 
1≢sssn : ∀ {n} → (x₁ : 1 ≡ suc (suc (suc n))) → ⊥
1≢sssn {n} = λ x₁ → invert (proof (T? Agda.Builtin.Bool.Bool.false)) (≡⇒≡ᵇ 1 (suc (suc (suc n))) x₁)

1≢ssn : ∀ {n} → (x₁ : 1 ≡ suc (suc n)) → ⊥
1≢ssn {n} = λ x₁ → invert (proof (T? false)) (≡⇒≡ᵇ 1 (suc (suc n)) x₁)

2≢sssn : ∀ {n} → (x₁ : 2 ≡ suc (suc (suc n))) → ⊥
2≢sssn {n} = λ x₁ → invert (proof (T? false)) (≡⇒≡ᵇ 2 (suc (suc (suc n))) x₁)




case3lemma : {a : Set} {x : a} → (λ (t : Vec a 1) → [ x ] ∷ t ∷ []) ≡ (λ t → subs (x ∷ t))
case3lemma {a} {x} = funext (λ y → localhelper x y)
  where 
    localhelper : {a : Set} (x : a) → (t : Vec a 1) → [ x ] ∷ t ∷ [] ≡ (subs ∘ (x ∷_ )) t
    localhelper {a} x (t ∷ []) = refl



map-compose : {a b c : Set} {n : ℕ} (f : b → c) (g : a → b) (xs : Vec a n) → map (f ∘ g) xs ≡ (map f ∘ map g) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) = 
  begin 
    map (f ∘ g) (x ∷ xs)  
  ≡⟨ refl ⟩
    (f ∘ g) x ∷ map (f ∘ g) xs
  ≡⟨ cong (λ w → (f ∘ g) x ∷ w) (map-compose f g xs) ⟩
    (f ∘ g) x ∷ (map f ∘ map g) xs
  ≡⟨ refl ⟩
    (map f ∘ map g) (x ∷ xs)
  ∎ 

ch-non-single : {a : Set} {n : ℕ} 
    → (k : ℕ) → (1+k≤1+n : suc k ≤ suc n) → (xs : Vec a (suc n))
    → suc k ≢ suc n 
    → Σ[ t ∈ B (Vec a (suc k)) k n ] 
      Σ[ u ∈ B (Vec a (suc k)) (suc k) n ]
          (ch (suc k) 1+k≤1+n xs ≡ N t u)
ch-non-single {n = n} k 1+k≤1+n (x ∷ xs) k≠n with suc k ≟ suc n
... | yes refl = ⊥-elim (k≠n refl) 
... | no k≠n = ( mapB (_∷_ x) (ch k (s≤s⁻¹ 1+k≤1+n) xs) 
               , ch (suc k) (lemma3 1+k≤1+n k≠n) xs
               , refl)

ch-non-single-expend : {a : Set} {n : ℕ} → (k : ℕ) → (1+k≤1+n : suc k ≤ suc n) → (sn≢n : ¬ suc k ≡ suc n) → (x : a) → (xs : Vec a n) → ch (suc k) 1+k≤1+n (x ∷ xs) ≡ N (mapB (x ∷_) (ch k (s≤s⁻¹ 1+k≤1+n) xs)) (ch (suc k) (lemma3 1+k≤1+n sn≢n) xs) 
ch-non-single-expend {a} {n} k 1+k≤1+n sn≢n x xs with suc k ≟ suc n 
... | yes refl = ⊥-elim (sn≢n refl)
... | no sk≠sn rewrite ≤-irrelevant  (lemma3 1+k≤1+n sk≠sn)  (lemma3 1+k≤1+n sn≢n) = refl

remove-suc-≢  : ∀ {n k} →  ¬ suc k ≡ suc n → ¬ k ≡ n 
remove-suc-≢  {n} {k} sk≡/sn refl = sk≡/sn refl

mapB-id : {a : Set} → {k n : ℕ} → (t : B a k n) → t ≡ mapB id t
mapB-id (T0 x) = refl
mapB-id (Tn x) = refl
mapB-id (N t₁ t₂) = Eq.cong₂ N (mapB-id t₁) (mapB-id t₂)

lemma-up-NN-expend : {a : Set} {k n : ℕ} 
  → (0<1+k : 0 < suc k) → (1+k<3+n : 1 + k < 3 + n) → (k≤2+n : k ≤ 2 + n) → (1+k≤2+n : suc k ≤ 2 + n)
  → (0<k : 0 < k) → (k<2+n : k < 2 + n) → (1+k<2+n : suc k < 2 + n)
  → (x : a) → (xs : Vec a (suc (suc n))) 
  → up 0<1+k 1+k<3+n (N (mapB (x ∷_) (ch k k≤2+n xs)) (ch (suc k)  1+k≤2+n xs)) ≡ N (zipBW snoc (up 0<k k<2+n (mapB (x ∷_) (ch k k≤2+n xs))) (ch (suc k) 1+k≤2+n xs)) (up 0<1+k 1+k<2+n (ch (suc k) 1+k≤2+n xs)) -- def. of up, since k ̸= 0 and 1 + k < length xs
lemma-up-NN-expend {_} {suc k} {zero} 0<1+k 1+k<3+n k≤2+n 1+k≤2+n 0<k k<2+n 1+k<2+n x (x₁ ∷ x₂ ∷ []) = ⊥-elim (sn≰0 (s≤s⁻¹ (s≤s⁻¹ 1+k<2+n))) -- N (mapB (_∷_ x₁) (ch (suc k) (s≤s⁻¹ 1+k≤2+n) (x₂ ∷ x₃ ∷ xs))) (ch (suc (suc k)) (lemma3 1+k≤2+n 2+k≠3+n) (x₂ ∷ x₃ ∷ xs))) = ch (suc k) 1+k≤2+n xs
lemma-up-NN-expend {_} {suc k} {suc n} 0<1+k 1+k<3+n k≤2+n 1+k≤2+n 0<k k<2+n 1+k<2+n x (x₁ ∷ x₂ ∷ x₃ ∷ xs) =
  begin   
    up 0<1+k 1+k<3+n (N (mapB (_∷_ x) t) u)
  ≡⟨ cong (λ w → up 0<1+k 1+k<3+n (N (mapB (_∷_ x) w) u)) (ch-non-single-expend k k≤2+n 1+k≠3+n x₁ (x₂ ∷ x₃ ∷ xs)) ⟩ -- expend t
    up 0<1+k 1+k<3+n (N (mapB (_∷_ x) (N (mapB (x₁ ∷_) t₁) t₂)) u) 
  ≡⟨ cong (λ w → up 0<1+k 1+k<3+n (N (mapB (_∷_ x) (N (mapB (x₁ ∷_) t₁) t₂)) w)) (ch-non-single-expend (suc k) 1+k≤2+n 2+k≠3+n x₁ (x₂ ∷ x₃ ∷ xs)) ⟩ -- expend u
    up 0<1+k 1+k<3+n (N (mapB (_∷_ x) (N (mapB (x₁ ∷_) t₁) t₂)) (N (mapB (_∷_ x₁) u₁) u₂)) 
  ≡⟨  refl  ⟩ -- def. of mapB
    up 0<1+k 1+k<3+n (N (N ((mapB (_∷_ x) ∘ mapB (x₁ ∷_)) t₁) (mapB (_∷_ x) t₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  cong (λ w → up 0<1+k w (N (N ((mapB (_∷_ x) ∘ mapB (x₁ ∷_)) t₁) (mapB (_∷_ x) t₂)) (N (mapB (_∷_ x₁) u₁) u₂))) (≤-irrelevant 1+k<3+n (s≤s 1+k≤2+n))  ⟩  -- rewrite ≤ 
    up 0<1+k (s≤s 1+k≤2+n) (N (N ((mapB (_∷_ x) ∘ mapB (x₁ ∷_)) t₁) (mapB (_∷_ x) t₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  refl  ⟩ -- def. of up
    N (zipBW snoc (up (s≤s z≤n) 1+k≤2+n (N ((mapB (_∷_ x) ∘ mapB (x₁ ∷_)) t₁) (mapB (_∷_ x) t₂))) (N (mapB (_∷_ x₁) u₁) u₂)) (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  cong(λ w → N (zipBW snoc (up w 1+k≤2+n (N ((mapB (_∷_ x) ∘ mapB (x₁ ∷_)) t₁) (mapB (_∷_ x) t₂))) (N (mapB (_∷_ x₁) u₁) u₂)) (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))) (≤-irrelevant (s≤s z≤n) 0<k)  ⟩ -- rewrite ≤ 
    N(zipBW snoc (up 0<k 1+k≤2+n  (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) (N (mapB (_∷_ x₁) u₁) u₂))(up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  cong(λ w → N (zipBW snoc  (up 0<k w (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) (N (mapB (_∷_ x₁) u₁) u₂)) (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))) (≤-irrelevant 1+k≤2+n k<2+n)  ⟩ -- rewrite ≤ 
    N (zipBW snoc (up 0<k k<2+n (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) (N (mapB (_∷_ x₁) u₁) u₂))(up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  cong(λ w → N (zipBW snoc (up 0<k k<2+n (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) w) (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))) pf1 ⟩ -- pf1 : (N (mapB (_∷_ x₁) u₁) u₂) = u
    N (zipBW snoc (up 0<k k<2+n (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) u) (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂))
  ≡⟨  cong(λ w → N (zipBW snoc (up 0<k k<2+n (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) u) w) pf2  ⟩ -- pf2 : (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂)) ≡ (up 0<1+k 1+k<2+n u)
    N (zipBW snoc (up 0<k k<2+n (N (mapB (_∷_ x) (mapB (x₁ ∷_) t₁)) (mapB (_∷_ x) t₂))) u) (up 0<1+k 1+k<2+n u)
  ≡⟨  refl  ⟩ -- def. of mapB
    N (zipBW snoc (up 0<k k<2+n (mapB (_∷_ x) (N (mapB (x₁ ∷_) t₁) t₂))) u) (up 0<1+k 1+k<2+n u)
  ≡⟨  cong (λ w → N (zipBW snoc (up 0<k k<2+n (mapB (_∷_ x) w)) u) (up 0<1+k 1+k<2+n u)) (sym (ch-non-single-expend k k≤2+n 1+k≠3+n x₁ (x₂ ∷ x₃ ∷ xs)))  ⟩ -- expend t
    N (zipBW snoc (up 0<k k<2+n (mapB (_∷_ x) ((ch (suc k) k≤2+n (x₁ ∷ x₂ ∷ x₃ ∷ xs))))) u) (up 0<1+k 1+k<2+n u)
  ≡⟨  refl  ⟩ -- def. of t
    N (zipBW snoc (up 0<k k<2+n (mapB (_∷_ x) t)) u) (up 0<1+k 1+k<2+n u)
  ∎
  where 
    1+k≠3+n : ¬ 1 + k ≡ 3 + n  
    1+k≠3+n refl =  (<-irrefl refl (k<2+n))

    2+k≠3+n : ¬ 2 + k ≡ 3 + n   
    2+k≠3+n refl = <-irrefl refl 1+k<2+n 
    
    t = (ch (suc k) k≤2+n (x₁ ∷ x₂ ∷ x₃ ∷ xs))
    u = ch (suc (suc k)) 1+k≤2+n (x₁ ∷ x₂ ∷ x₃ ∷ xs)
    t₁ = ch k (s≤s⁻¹ k≤2+n) (x₂ ∷ x₃ ∷ xs)
    t₂ = ch (suc k) (lemma3 k≤2+n 1+k≠3+n) (x₂ ∷ x₃ ∷ xs)
    u₁ = ch (suc k) (s≤s⁻¹ 1+k≤2+n) (x₂ ∷ x₃ ∷ xs)
    u₂ = ch (suc (suc k)) (lemma3 1+k≤2+n 2+k≠3+n) (x₂ ∷ x₃ ∷ xs)
    
    pf1 : (N (mapB (_∷_ x₁) u₁) u₂) ≡ u
    pf1 = 
      begin 
        (N (mapB (_∷_ x₁) (ch (suc k) (s≤s⁻¹ 1+k≤2+n) (x₂ ∷ x₃ ∷ xs))) (ch (suc (suc k)) (lemma3 1+k≤2+n 2+k≠3+n) (x₂ ∷ x₃ ∷ xs)))
      ≡⟨ sym (ch-non-single-expend (suc k) 1+k≤2+n 2+k≠3+n x₁ (x₂ ∷ x₃ ∷ xs)) ⟩
        ch (suc (suc k)) 1+k≤2+n (x₁ ∷ x₂ ∷ x₃ ∷ xs)
      ∎
    pf2 : (up (s≤s z≤n) (s≤s (bounded u₂)) (N (mapB (_∷_ x₁) u₁) u₂)) ≡ (up 0<1+k 1+k<2+n u)
    pf2 rewrite pf1 
        rewrite ≤-irrelevant (s≤s z≤n) 0<1+k
        rewrite ≤-irrelevant  (s≤s (bounded (ch (suc (suc k)) (s≤s (lemma3 (s≤s⁻¹ 1+k≤2+n) (λ eq → 2+k≠3+n (cong suc eq)))) (x₂ ∷ x₃ ∷ xs)))) 1+k<2+n
        = refl

thm1' : {k n : ℕ} {a : Set} → (p : 0 < k) → (q : k < n) → (r1 : k ≤ n) → (r2 : suc k ≤ n) → (xs : Vec a n) → up p q (ch k r1 xs) ≡ mapB subs (ch (suc k) r2 xs) 
thm1' {k} {n} p q r1 r2 xs with suc k ≟ n | k ≟ 1
thm1' {.1} {.2} p q r1 r2 (x ∷ xs ∷ []) | yes refl | yes refl = refl -- Case 1: suc k ≡ n and k ≡ 1
thm1' {suc zero} {.2} p q r1 r2 (x ∷ x₁ ∷ xs) | yes refl | no ¬p = ⊥-elim (¬p refl) 
thm1' {k} {suc .zero} p q r1 r2 (x ∷ []) | no ¬p | no ¬p₁ = ⊥-elim (h1 r2 p) -- suc k ≤ 1 1 ≤ k
thm1' {k} {suc (suc .zero)} p q r1 r2 (x ∷ x₁ ∷ []) | no ¬p | no ¬p₁ = ⊥-elim (h2 r2 p ¬p₁)
thm1' {suc k} {suc (suc (suc n))} p q r1 r2 (x ∷ x₁ ∷ x₂ ∷ xs) | no ¬p | no ¬p₁ = 
  begin 
    up p q (ch (suc k) r1 (x ∷ x₁ ∷ x₂ ∷ xs)) 
  ≡⟨ cong (λ w → up p q w) (ch-non-single-expend k r1 1+k≠3+n x (x₁ ∷ x₂ ∷ xs)) ⟩ -- def. of ch, since 1 + k < length (x : xs) -- 1+k≠3+n 
    up p q (N (mapB (x ∷_) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs))) (ch (suc k) (lemma3 r1 1+k≠3+n) ((x₁ ∷ x₂ ∷ xs))))
  ≡⟨ lemma-up-NN-expend p q (s≤s⁻¹ r1) (lemma3 r1 1+k≠3+n) 0<k (s≤s⁻¹ r2) (s≤s (s≤s k≤n)) x (x₁ ∷ x₂ ∷ xs) ⟩
    N (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (_∷_ x) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (lemma3 r1 1+k≠3+n) (x₁ ∷ x₂ ∷ xs))) (up p (s≤s (s≤s k≤n)) (ch (suc k) (lemma3 r1 1+k≠3+n) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ cong(λ w → N (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (_∷_ x) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) w (x₁ ∷ x₂ ∷ xs))) (up p (s≤s (s≤s k≤n)) (ch (suc k) w (x₁ ∷ x₂ ∷ xs)))) (≤-irrelevant (lemma3 r1 1+k≠3+n) (s≤s⁻¹ r2)) ⟩ -- rewrite (lemma3 r1 1+k≠3+n) to (s≤s⁻¹ r2)
    N (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (_∷_ x) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))(up p (s≤s (s≤s k≤n)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ cong(λ w → N (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (_∷_ x) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (up w (s≤s (s≤s k≤n)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))) (≤-irrelevant p (s≤s z≤n)) ⟩ -- rewrite p to (s≤s z≤n)
    N (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (x ∷_) (ch k (s≤s⁻¹ (r1)) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (up (s≤s z≤n) (s≤s (s≤s k≤n)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) -- def. of up, since k ̸= 0 and 1 + k < length xs
  ≡⟨ cong (λ w → N w (up (s≤s z≤n) (s≤s (s≤s k≤n)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))) theFirstArg ⟩
    N (mapB (subs ∘ _∷_ x) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (up (s≤s z≤n) (s≤s (s≤s k≤n)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ cong (λ w →  N (mapB (subs ∘ _∷_ x) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) w) (thm1' (s≤s z≤n) (s≤s (s≤s k≤n)) (s≤s⁻¹ r2) (s≤s (s≤s k≤n)) (x₁ ∷ x₂ ∷ xs)) ⟩ -- induction
    N (mapB (subs ∘ (x ∷_ )) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (mapB subs (ch (suc (suc k)) (s≤s (s≤s k≤n)) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ cong (λ w → N (mapB (subs ∘ (x ∷_)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (mapB subs (ch (suc (suc k)) w (x₁ ∷ x₂ ∷ xs)))) (≤-irrelevant (s≤s (s≤s k≤n)) (lemma3 r2 ¬p)) ⟩ 
    N (mapB (subs ∘ (x ∷_ )) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (mapB subs (ch (suc (suc k)) (lemma3 r2 ¬p) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ mapB-subs ⟩
    mapB subs (N (mapB (x ∷_) (ch (suc k) (s≤s⁻¹ r2) ((x₁ ∷ x₂ ∷ xs)))) (ch ((suc (suc k))) (lemma3 r2 ¬p) (x₁ ∷ x₂ ∷ xs)))
  ≡⟨ cong (λ w → mapB subs w) (sym (ch-non-single-expend (suc k) r2 ¬p x ((x₁ ∷ x₂ ∷ xs)))) ⟩
    mapB subs (ch (suc (suc k)) r2 (x ∷ x₁ ∷ x₂ ∷ xs))
  ∎
  where   

    1+k≠3+n : ¬ suc k ≡ suc (suc (suc n))
    1+k≠3+n refl = <-irrefl refl r2

    --- helper of 0 < k
    1+n≠1⇒0<n : ∀ {v} → ¬ suc v ≡ 1 → 0 < v 
    1+n≠1⇒0<n {zero} p = ⊥-elim (p refl)
    1+n≠1⇒0<n {suc v} p = s≤s z≤n
    
    0<k : 0 < k 
    0<k = 1+n≠1⇒0<n ¬p₁
    -- helper of k≤n
    k≢sn∧k≤sn⇒k≤n : ∀ {k n} → ¬ k ≡ suc n → k ≤ suc n → k ≤ n
    k≢sn∧k≤sn⇒k≤n {k} {n} k≢sucn k≤sucn = ≤-pred (≤∧≢⇒< k≤sucn k≢sucn)

    k≤n : k ≤ n 
    k≤n = k≢sn∧k≤sn⇒k≤n (remove-suc-≢   (remove-suc-≢ (¬p))) (s≤s⁻¹ (s≤s⁻¹ r2))



    theFirstArg : (zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (x ∷_) (ch k (s≤s⁻¹ (r1)) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) ≡ mapB (subs ∘ (x ∷_)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))
    theFirstArg = 
      begin 
        zipBW snoc (up 0<k (s≤s⁻¹ r2) (mapB (x ∷_) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))
      ≡⟨ cong (λ w → zipBW snoc w (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)) )  (up-natural (x ∷_) 0<k (s≤s⁻¹ r2) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs))) ⟩ -- up natural
        zipBW snoc (mapB (map (x ∷_)) (up 0<k (s≤s⁻¹ r2) (ch k (s≤s⁻¹ r1) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))
      ≡⟨ cong (λ w → zipBW snoc (mapB (map (x ∷_)) w ) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))) (thm1' 0<k (s≤s⁻¹ r2) (s≤s⁻¹ r1) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)) ⟩
        zipBW snoc (mapB (map (x ∷_)) (mapB subs (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)))) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)) -- induction
      ≡⟨ cong (λ w → zipBW snoc w u) (sym (mapB-compose (map (_∷_ x)) subs u)) ⟩ -- mapB-compose
        zipBW snoc (mapB (map (x ∷_) ∘ subs) u) u
      ≡⟨ cong (λ w → zipBW snoc (mapB (map (x ∷_) ∘ subs) u) w) (mapB-id u) ⟩ -- u ≡ mapB id u
        zipBW snoc (mapB (map (x ∷_) ∘ subs) u) (mapB id u)
      ≡⟨ sym (zipBW-natural-eq-input (subs ∘ (x ∷_)) ((λ x₃ x₄ → x₄))  snoc ( map (x ∷_) ∘ subs) id (λ x₃ → pf1 x x₃) u ) ⟩ -- pf1
        mapB (λ x₃ → subs (x ∷ x₃)) (zipBW (λ x₃ x₄ → x₄) u u)
      ≡⟨ cong (λ w → mapB (λ x₃ → subs (x ∷ x₃)) w) (pf2 u) ⟩ 
        mapB (subs ∘ (x ∷_)) u
      ≡⟨ refl ⟩
        mapB (subs ∘ (x ∷_)) (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))
      ∎
      where     
        u = (ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs))
      

        pf1 : {a : Set} {k : ℕ} → (x : a) → (xs : Vec a (suc k)) → subs (x ∷ xs) ≡ snoc (map (x ∷_) (subs xs)) (id xs)
        pf1 {_} {k} x (x₁ ∷ xs) = refl

        pf2 : {a : Set} → {k n : ℕ} → (t : B a k n) → (zipBW (λ x₃ x₄ → x₄) t t) ≡ t 
        pf2 {_} {.0} {n} (T0 x) = refl
        pf2 {_} {.(suc _)} {.(suc _)} (Tn x) = refl
        pf2 {_} {.(suc _)} {.(suc _)} (N t t₁) rewrite  pf2 t | pf2 t₁ = refl


    u₁ = ch (suc k) (s≤s⁻¹ r2) (x₁ ∷ x₂ ∷ xs)
    u₂ = ch (suc (suc k)) (lemma3 r2 ¬p) (x₁ ∷ x₂ ∷ xs)

    mapB-subs : N (mapB (subs ∘ (x ∷_ )) u₁) (mapB subs u₂) ≡  mapB subs (N (mapB (x ∷_) u₁) u₂)
    mapB-subs = cong (λ w → N w (mapB subs u₂)) (mapB-compose subs (x ∷_) u₁)


thm1' {suc k} {suc (suc (suc n))} {a} p q r1 r2 (x ∷ xs@(y ∷ ys@(z ∷ zs))) | yes refl | no  k≢1 = -- Case 2: suc k ≡ n and k ≢ 1 (n > 2)
  begin 
    up p q (ch (suc (suc n)) r1 (x ∷ xs))
  ≡⟨ cong (up p q) (lemma-ch-neq-rec r1 ssn≠sssn x xs) ⟩ 
    up p q (N (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ r1) xs)) (ch (suc (suc n)) (lemma3 r1 ssn≠sssn) xs))
  ≡⟨ cong (up p q) (cong (N ((mapB (x ∷_) (ch (suc n) (s≤s⁻¹ r1) xs)))) (lemma-ch-eq-Tn (suc n) ( lemma3 r1 ssn≠sssn) xs)) ⟩ -- def. of up 
    up p q (N (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ r1) (y ∷ ys))) (Tn xs))
  ≡⟨ cong (λ w → up p q (N (mapB (x ∷_) w) (Tn xs))) (lemma-ch-neq-rec (s≤s⁻¹ r1) sn≠ssn y ys) ⟩ -- ch suc n p xs sucsucn
    up p q (N (mapB (x ∷_) (N (mapB ((y ∷_)) (ch n (s≤s⁻¹( s≤s⁻¹ r1)) ys)) (ch (suc n) (lemma3 (s≤s⁻¹ r1) sn≠ssn) ys))) (Tn xs))
  ≡⟨ refl ⟩
    Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) ((mapB (x ∷_) (N (mapB ((y ∷_)) (ch n (s≤s⁻¹( s≤s⁻¹ r1)) ys)) (ch (suc n) (lemma3 (s≤s⁻¹ r1) sn≠ssn) ys)))))) xs)
  ≡⟨ cong (λ w → Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) (mapB (x ∷_) w))) xs)) (sym (lemma-ch-neq-rec (s≤s⁻¹ r1) sn≠ssn y (z ∷ zs))) ⟩
    Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ r1) xs)))) xs)
  ≡⟨ cong (λ w → Tn (snoc (unTn w) xs)) (up-natural (x ∷_) (s≤s z≤n) ≤-refl (ch (suc n) (s≤s⁻¹ r1) xs)) ⟩ -- up natural  -- up (B (x:) (ch k xs) = B (L (x:)) (up (ch k xs)) -- up 0<k k<n (mapB f t) ≡ mapB (map f) (up 0<k k<n t)
    Tn (snoc (unTn (mapB (map (x ∷_)) (up (s≤s z≤n) (≤-refl) (ch (suc n) (s≤s⁻¹ r1) xs)) )) xs) 
  ≡⟨ cong (λ w → Tn (snoc (unTn (mapB (map (x ∷_)) w)) xs)) (thm1' (s≤s z≤n) (≤-refl) (s≤s⁻¹ r1) (s≤s⁻¹ r2) xs) ⟩  -- induction
    Tn (snoc (unTn (mapB (map (x ∷_)) (mapB subs (ch (suc (suc n)) (s≤s⁻¹ r2) xs)) )) xs) 
  ≡⟨ cong (λ w → Tn (snoc (unTn (mapB (map (x ∷_)) (mapB subs w) )) xs)) (lemma-ch-eq-Tn (suc n) (s≤s⁻¹ r2) xs) ⟩  -- ch n n = Tn ..
    Tn (snoc (unTn {n = n} (mapB (map (x ∷_)) (mapB subs (Tn xs)))) xs) -- Vec a (suc (suc n₁)), Vec a (suc (suc n₁))
  ≡⟨ refl ⟩  -- def. of mapB and map 
    Tn (snoc (map (x ∷_) (subs xs)) xs)  -- (unTn (mapB (map (x ∷_)) (mapB subs (Tn xs)))) map f (map g x)
  ≡⟨ refl ⟩  -- def. of subs
    Tn (snoc (map (x ∷_) (subs xs)) xs)  -- (unTn (mapB (map (x ∷_)) (mapB subs (Tn xs)))) map f (map g x)
  ≡⟨ refl ⟩  -- def. of subs
    Tn (subs (x ∷ xs))
  ≡⟨ refl ⟩  -- def of mapB
    mapB subs (Tn (x ∷ xs))
  ≡⟨ sym (cong (mapB subs) (lemma-ch-eq-Tn ((suc k)) r2 ((x ∷ xs)))) ⟩  -- def of ch
    mapB subs (ch (suc (suc (suc n))) r2 (x ∷ xs))  
  ∎

thm1' {suc k} {n = suc (suc (suc n))} {a} p q r1 r2 (x ∷ xs@(y ∷ ys@(z ∷ zs))) | no  n≢sk | yes refl =  -- Case 3: suc k ≢ n and k ≡ 1
    begin 
      up p q (ch 1 r1 (x ∷ xs)) -- r1 : 1 ≤ 3+n, n≢sk : 2 != 3 + n
    ≡⟨ refl ⟩ 
      up p q (N (mapB (x ∷_) (ch 0 (s≤s⁻¹ r1) xs)) (ch 1 ( lemma3 r1 1≢sssn ) xs)) -- n≢sk : ¬ 2 ≡ suc (suc (suc n)) , q : ¬ suc k ≡ suc  n))
    ≡⟨ refl ⟩ -- def. of ch
      up p q (N (mapB (x ∷_) (T0 [])) (ch 1 ( lemma3 r1 1≢sssn ) xs)) -- n≢sk : ¬ 2 ≡ suc (suc (suc n)) , q : ¬ suc k ≡ suc  n))
    ≡⟨ refl ⟩  -- def of mapB
      up p q (N (T0 [ x ]) (ch 1 ( lemma3 r1 1≢sssn ) xs)) -- uu = (ch 1 ( lemma3 r1 bot ) xs) 
    ≡⟨ refl ⟩ -- ch 1 ( lemma3 r1 bot ) (y ∷ ys) = ch {suc n} 1 p (x ∷ xs) = N ((mapB (x ∷_) (ch 0 (s≤s⁻¹ p) xs))) ((ch 1 (lemma3 p n≢sk) xs))
      up p q (N (T0 [ x ]) (N ((mapB (y ∷_) (ch 0 (s≤s⁻¹ (lemma3 r1 1≢sssn)) ys))) ((ch 1 (lemma3 (lemma3 r1 1≢sssn) 1≢ssn) ys))))   
    ≡⟨ refl ⟩  -- def of ch -- map
      up p q (N (T0 [ x ]) (N (T0 [ y ]) (ch 1 (lemma3 (lemma3 r1 1≢sssn) 1≢ssn) ys)) )
    ≡⟨ refl ⟩  -- use uu and uu' for clearity
      up p q (N (T0 [ x ]) uu )
    ≡⟨ refl ⟩ 
      N (mapB (λ t → [ x ] ∷ t ∷ []) uu) (up ≤-refl (s≤s (bounded uu')) (ch 1 ( lemma3 r1 1≢sssn ) xs)) -- uu = ch 1 ( lemma3 r1 bot ) xs
    ≡⟨ cong (N (mapB (λ t → [ x ] ∷ t ∷ []) uu)) (thm1' ≤-refl (s≤s (bounded uu')) (lemma3 r1 1≢sssn) (s≤s (s≤s z≤n)) xs) ⟩  -- induction  up p q (ch k r1 xs) ≡ mapB subs (ch (suc k) r2 xs) -- up p q (ch 1 r1 xs) 
      N (mapB (λ t → [ x ] ∷ t ∷ []) uu) (mapB subs (ch 2 (s≤s (s≤s z≤n)) xs))
    ≡⟨ cong (λ f → N (mapB f uu) (mapB subs (ch 2 (s≤s (s≤s z≤n)) xs))) case3lemma ⟩  -- the "see below"  --  
      N (mapB (subs ∘ (x ∷_ )) uu) (mapB subs (ch 2 (s≤s (s≤s z≤n)) xs))
    ≡⟨ cong (λ t → N t (mapB subs (ch 2 (s≤s (s≤s z≤n)) xs))) (mapB-compose subs ((x ∷_)) uu) ⟩ -- def of mapB   
      mapB subs (N (mapB (x ∷_ ) uu) (ch 2 (s≤s (s≤s z≤n)) xs))
    ≡⟨ refl ⟩  -- uu = (N (T0 [ y ]) (ch 1 (lemma3 (lemma3 r1 bot) bot') ys))
      mapB subs (N (mapB (x ∷_) (N (T0 [ y ]) (ch 1 (lemma3 (lemma3 r1 1≢sssn) 1≢ssn) ys))) (ch 2 (s≤s (s≤s z≤n)) xs))
    ≡⟨ cong (λ w → mapB subs (N (mapB (x ∷_) (N (T0 [ y ]) (ch 1 (lemma3 w 1≢ssn) ys)))  (ch 2 (s≤s (s≤s z≤n)) xs))) (≤-irrelevant (lemma3 r1 1≢sssn) (s≤s⁻¹ r2)) ⟩  -- lemma3 r1 1≢sssn  = s≤s⁻¹ r2
      mapB subs (N (mapB (x ∷_) (N (T0 [ y ]) (ch 1 (lemma3 (s≤s⁻¹ r2) 1≢ssn) ys))) (ch 2 (s≤s (s≤s z≤n)) xs))
    ≡⟨ cong(λ w → mapB subs (N (mapB (x ∷_) (N (T0 [ y ]) (ch 1 (lemma3 (s≤s⁻¹ r2) 1≢ssn) ys))) (ch 2 w xs))) (≤-irrelevant ((s≤s (s≤s z≤n))) (lemma3 r2 2≢sssn))  ⟩         
      mapB subs (N (mapB (x ∷_) (N (T0 ([ y ])) (ch 1 (lemma3 (s≤s⁻¹ r2) 1≢ssn) ys))) (ch 2 (lemma3 r2 2≢sssn) xs)) -- N (mapB (x ∷_) (ch 1 (s≤s⁻¹ r2) xs)) (ch 2 (lemma3 r2 k≢sk) xs)
    ≡⟨ refl ⟩ 
      mapB subs (N (mapB (x ∷_) (ch 1 (s≤s⁻¹ r2) (y ∷ ys))) (ch 2 (lemma3 r2 2≢sssn) xs)) -- N (mapB (x ∷_) (ch 1 (s≤s⁻¹ r2) xs)) (ch 2 (lemma3 r2 k≢sk) xs)
    ≡⟨ refl ⟩ 
      mapB subs (ch 2 r2 (x ∷ xs)) -- N (mapB (x ∷_) (ch 1 (s≤s⁻¹ r2) xs)) (ch 2 (lemma3 r2 k≢sk) xs)
  ∎
  where 
    uu  = N (T0 [ y ]) (ch 1 (lemma3 (lemma3 r1 1≢sssn) 1≢ssn) ys)
    uu' = (ch 1 (lemma3 (lemma3 r1 1≢sssn) 1≢ssn) ys)
      
thm1' {.1} {suc zero} p q r1 r2 (x ∷ []) | no ¬p | yes refl = ⊥-elim (2≰1 r2)
  where 
    2≰1 : 2 ≤ 1 → ⊥  
    2≰1 (s≤s ())
thm1' {.1} {suc (suc zero)} p q r1 r2 (x ∷ x₁ ∷ xs) | no ¬p | yes refl = ⊥-elim (¬p refl)

-- thm2

suc-< : ∀ {n m : ℕ} → suc n < m → n < m
suc-< {zero} {suc m} p = s≤s z≤n
suc-< {suc n} {suc m} p = s≤s (suc-< (≤-pred p))

pn+1<ssm : ∀ {n m : ℕ} → pred (suc n) + 1 < suc (suc m) →  pred n + 1 < suc (suc m)
pn+1<ssm {zero} {m} p = s≤s (s≤s z≤n)
pn+1<ssm {suc n} {m} p = suc-< p


psn+1<ssn : ∀ {n} → pred (suc n) + 1 < suc (suc n) -- n+1 < 2+n
psn+1<ssn {n} = s≤s (subst (λ w → w ≤ suc n) (sym (n+1≡sucn n)) ≤-refl)

ex : {a : Set} → Vec a 1 → a 
ex (x ∷ []) = x 
postulate
  X : Set 
  Y : Set
  f : X → Y
  g : {n : ℕ} → Vec Y (suc n) → Y

td : (n : ℕ) → (xs : Vec X (suc n)) → Y
td zero x = f (ex x)  
td (suc n) xs = g (map (td n) (subs xs))

-- td n = td' n ∘ map f
td' : (n : ℕ) → Vec Y (suc n) → Y
td' zero = ex
td' (suc n) = g ∘ map (td' n) ∘ subs

repeat : {X : Set} → (n : ℕ) → (X → X) → X → X
repeat zero f = id
repeat (suc n) f = repeat n f ∘ f

tt1 : ∀ {k n} (1≤k : 1 ≤ k) →  0 < n + k
tt1 {suc k} {zero} 1≤k = s≤s z≤n
tt1 {suc k} {suc n} 1≤k = 0<1+n

tt2 : ∀ {k m} →  (n : ℕ) → (n+k<m : pred (suc n) + k < m) → pred n + k < m
tt2 {k} {m} zero n+k<m = n+k<m
tt2 {k} {m} (suc n) n+k<m = suc-< n+k<m


repeatUp' : {k : ℕ} {m : ℕ} → (n : ℕ) → (1≤k : 1 ≤ k) → (n+k<m : pred n + k < m) →  B Y k m → B Y (n + k) m
repeatUp'  zero _ _ t = t  -- id       
repeatUp' {k} (suc n)  1≤k n+k<m t = (mapB g ∘ up (tt1 1≤k) n+k<m ) (repeatUp' n  1≤k (tt2 n n+k<m) t)  


rewrite-type : ∀ {a n k} → B a (n + 1) k → B a (suc n) k
rewrite-type {a} {n} {k} x = subst (λ m → B a m k) (n+1≡sucn n) x

invrewrite-type : ∀ {a n k} → B a (suc n) k → B a (n + 1) k
invrewrite-type {a} {n} {k} x = subst (λ m → B a m k) (sym (n+1≡sucn n)) x


bu : (n : ℕ) → (xs : Vec X (suc n)) → Y
bu zero xs = (unTn ∘ mapB ex ∘ ch 1 (s≤s z≤n) ∘ (map f) ) xs -- (repeatUp)⁰ = id
bu (suc n) xs = (unTn ∘ rewrite-type ∘ repeatUp' (suc n) (≤-refl) (psn+1<ssn {n = n}) ∘ mapB ex ∘ ch 1 (s≤s z≤n) ∘ (map f) ) xs 

-- properties

subst-sym-cancel : ∀ {A : Set} {x y : A} (P : A → Set) → (eq : x ≡ y) → subst P eq ∘ subst P (sym eq) ≡ id
subst-sym-cancel P refl = refl

rewrite-invrewrite-t≡t : ∀ {a n k} → (t : B a (suc n) k) → (rewrite-type ∘ invrewrite-type) t ≡ t 
rewrite-invrewrite-t≡t {a} {n} {k} t = 
  begin 
    (rewrite-type ∘ invrewrite-type) t
  ≡⟨ refl ⟩
    (subst (λ m → B a m k) (n+1≡sucn n) ∘ subst (λ m → B a m k) (sym (n+1≡sucn n))) t
  ≡⟨ cong (λ w → w t) (subst-sym-cancel ((λ m → B a m k)) (n+1≡sucn n)) ⟩
    t
  ∎

rewrite-invrewrite≡id : ∀ {a n k} → (rewrite-type {n = n} {k = k} ∘ invrewrite-type {n = n} {k = k}) ≡ id 
rewrite-invrewrite≡id {a} {n} {k} = 
  begin 
    rewrite-type {n = n} {k = k} ∘ invrewrite-type {n = n} {k = k}
  ≡⟨ refl ⟩
    (subst (λ m → B a m k) (n+1≡sucn n) ∘ subst (λ m → B a m k) (sym (n+1≡sucn n))) 
  ≡⟨ subst-sym-cancel ((λ m → B a m k)) (n+1≡sucn n) ⟩
    id
  ∎ 
-- naturality

-- map (map f) ∘ subs = subs ∘ map f
subs-natural : (n : ℕ) → (xs : Vec X (suc n)) → (map (map f) ∘ subs) xs ≡ (subs ∘ map f) xs
subs-natural zero (x ∷ []) = refl
subs-natural (suc n) (x ∷ xs@(y ∷ ys)) = 
  begin 
    (map (map f) ∘ subs) (x ∷ xs)
  ≡⟨ refl ⟩ 
    (map (map f)) (snoc (map (x ∷_) (subs xs)) xs )
  ≡⟨ snoc-natural (map f) (map (x ∷_) (subs (y ∷ ys))) (y ∷ ys) ⟩ -- snoc naturality
    snoc (map (map f) (map (x ∷_) (subs xs))) (map f xs) 
  ≡⟨ cong (λ w → snoc w (map f xs)) (helperlem3 n (suc n) x (subs xs)) ⟩ 
    snoc (map (f x ∷_) (map (map f) (subs xs))) (map f xs)
  ≡⟨ cong (λ w → snoc (map (f x ∷_) w) (map f xs)) (subs-natural n xs) ⟩ 
    snoc (map (f x ∷_) (subs (map f xs))) (map f xs)
  ≡⟨ refl ⟩ 
    subs (f x ∷ (map f xs ))
  ≡⟨ refl ⟩ 
    (subs ∘ map f) (x ∷ xs)
  ∎ 
  where 
    helperlem3 : (n : ℕ) → (m : ℕ) →  (x : X) → (xs : Vec (Vec X n) m) → (map (map f) (map (x ∷_) xs)) ≡ (map (f x ∷_) (map (map f) xs))
    helperlem3 zero m x (y ∷ []) = refl
    helperlem3 n zero x [] = refl
    helperlem3 (suc n) (suc .zero) x (xs ∷ []) = refl
    helperlem3 n (suc (suc n₁)) x (xs ∷ xs₁ ∷ xs₂) = cong (λ w → (f x ∷ map f xs) ∷ (f x ∷ map f xs₁) ∷ w) (helperlem3 n n₁ x xs₂)

remove-invrewrite-type : ∀ {a n k} → (t : B a (suc n) k) → invrewrite-type t HEq.≅ t 
remove-invrewrite-type {a} {n} {k} t = 
  HEq.≅-Reasoning.begin
    subst (λ m₁ → B a m₁ k) (sym (n+1≡sucn n)) t
  HEq.≅-Reasoning.≅⟨  HEq.≡-subst-removable (λ m₁ → B a m₁ k) (sym (n+1≡sucn n)) t ⟩
    t
  HEq.≅-Reasoning.∎ 

remove-rewrite-type : ∀ {a n k} → (t : B a (n + 1) k) → rewrite-type t HEq.≅ t 
remove-rewrite-type {a} {n} {k} = HEq.≡-subst-removable (λ m → B a m k) (n+1≡sucn n) 


up-eq : {a : Set} → ∀ {n k n' k'} → (t1 : B a k n) → (t2 : B a k' n') → (p : 0 < k) → (q : k < n) → (p' : 0 < k') → (q' : k' < n') → (eqk : k HEq.≅ k') → (eqn : n HEq.≅ n') → (eq : t1 HEq.≅ t2) → up p q t1 HEq.≅ up p' q' t2 
up-eq {a} {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (Tn x) (Tn x₁) p q p' q' eqk eqn eq = ⊥-elim (n≮n (suc _) q) -- 
up-eq {a} {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (Tn x) (N t2 t3) p q p' q' eqk eqn eq = ⊥-elim ((n≮n (suc _) q))
up-eq {a} {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (N t1 t2) (Tn x) p q p' q' eqk eqn eq = ⊥-elim ((n≮n (suc _) q'))
up-eq {a} {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (N t1 t2) (N t3 t4)p q p' q'  HEq.refl HEq.refl HEq.refl = HEq.cong₂ (λ w1 w2 → up w1 w2 (N t1 t2)) (HEq.≡-to-≅ (≤-irrelevant p p')) (HEq.≡-to-≅ (≤-irrelevant q q'))


mapB-up-eq : ∀ {n k n' k'}  → (t1 : B Y k n) → (t2 : B Y k' n') → (p : 0 < k) → (q : k < n) → (p' : 0 < k') → (q' : k' < n') → 
              (eqk : k HEq.≅ k') → (eqn : n HEq.≅ n') →  (eq : t1 HEq.≅ t2) → mapB g (up p q t1) HEq.≅ mapB g (up p' q' t2) 
mapB-up-eq {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (Tn x) (Tn x₁) p q p' q' eqk eqn eq  = ⊥-elim (n≮n (suc _) q)
mapB-up-eq {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (Tn x) (N t2 t3) p q p' q' eqk eqn eq  = ⊥-elim (n≮n (suc _) q)
mapB-up-eq {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (N t1 t2) (Tn x) p q p' q' eqk eqn eq  = ⊥-elim (n≮n (suc _) q')
mapB-up-eq {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (N t1 t2) (N t3 t4) p q p' q' HEq.refl HEq.refl HEq.refl = HEq.cong (mapB g) (up-eq ((N t1 t2)) ((N t3 t4)) p q p' q' HEq.refl HEq.refl HEq.refl)

psn+1<ssm⇒sn≤ssm : ∀ {n m} → (pn+1<m : pred (suc n) + 1 < suc (suc m)) →  suc n ≤ suc (suc m)
psn+1<ssm⇒sn≤ssm {n} {m} pn+1<m = <⇒≤ (subst (λ x → x < suc (suc m)) (+-comm n 1) pn+1<m)

ssn≤ssm⇒pn+1<ssm : ∀ {n m} → (ssn≤ssm : suc (suc n) ≤ suc (suc m)) → pred n + 1 < suc (suc m)
ssn≤ssm⇒pn+1<ssm {zero} {m} ssn≤ssm = s≤s (s≤s z≤n)
ssn≤ssm⇒pn+1<ssm {suc n} {m} ssn≤ssm = s≤s (subst (λ x → x ≤ suc m) (+-comm 1 n) (≤-trans (s≤s⁻¹ (s≤s⁻¹ ssn≤ssm )) (n≤1+n m)))
  
lemma1HEQ : {n m : ℕ} → (xs : Vec X m) → (sn≤m : suc n ≤ m) → (pn+1<m : pred n + 1 < m) → (1≤m : 1 ≤ m) → (invrewrite-type ∘ mapB (td' n) ∘ ch (suc n) sn≤m ∘ map f) xs HEq.≅ (repeatUp' n  ≤-refl pn+1<m ∘ mapB ex ∘ ch 1 1≤m ∘ (map f)) xs
lemma1HEQ {zero} {suc zero} (x ∷ xs) sn≤m pn+1<m 1≤m = HEq.refl
lemma1HEQ {zero} {suc (suc m)} (x ∷ xs) sn≤m pn+1<m 1≤m = HEq.refl
lemma1HEQ {suc n} {suc zero} (x ∷ []) sn≤m pn+1<m 1≤m = ⊥-elim (n≮0 (s≤s⁻¹ sn≤m))
lemma1HEQ {suc n} {suc (suc m)} (x ∷ xs) sn≤m pn+1<m 1≤m = 
  HEq.≅-Reasoning.begin
    (invrewrite-type ∘ mapB (td' (suc n)) ∘ ch (suc (suc n)) sn≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.refl ⟩ -- def. of td'
    (invrewrite-type ∘ mapB (g ∘ map (td' n) ∘ subs) ∘ ch (suc (suc n)) sn≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (invrewrite-type w))  (HEq.≡-to-≅ (mapB-compose (g ∘ map (td' n)) subs ((ch (suc (suc n)) sn≤m ∘ map f) (x ∷ xs)))) ⟩ -- mapB f.g = mapB f . mapB g
    (invrewrite-type ∘ mapB (g ∘ map (td' n)) ∘ mapB subs ∘ ch (suc (suc n)) sn≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (invrewrite-type ∘ mapB (g ∘ map (td' n))) w) (HEq.sym (HEq.≡-to-≅ (thm1' (s≤s z≤n) sn≤m (psn+1<ssm⇒sn≤ssm pn+1<m) sn≤m (f x ∷ map f xs)))) ⟩ -- thm1
    (invrewrite-type ∘ mapB (g ∘ (map (td' n))) ∘ (up (s≤s z≤n) sn≤m ∘  (ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m))) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → invrewrite-type w) (HEq.≡-to-≅ (mapB-compose g ((map (td' n))) ((((up (s≤s z≤n) sn≤m ∘  (ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m)))) ∘ map f) (x ∷ xs)))) ⟩ -- mapB (g . f) = mapB g . mapB f
    (invrewrite-type ∘ mapB g ∘ mapB (map (td' n)) ∘ (up (s≤s z≤n) sn≤m ∘  (ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m))) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨  HEq.cong (λ w → (invrewrite-type ∘ mapB g) w) (HEq.sym (HEq.≡-to-≅ (up-natural (td' n) (s≤s z≤n) sn≤m ((((ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m))) ∘ map f) (x ∷ xs)))))  ⟩ -- up natural
    (invrewrite-type ∘ mapB g ∘ up (s≤s z≤n) sn≤m ∘ mapB (td' n) ∘ ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong(λ w → (invrewrite-type ∘ mapB g ∘ up (s≤s z≤n) sn≤m ∘ w ∘ mapB (td' n) ∘ ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m) ∘ map f) (x ∷ xs)) (HEq.≡-to-≅ (sym rewrite-invrewrite≡id)) ⟩ -- rewrite-type ∘  invrewrite-type = id
    (invrewrite-type ∘ mapB g ∘ up (s≤s z≤n) sn≤m ∘ rewrite-type ∘ invrewrite-type ∘ mapB (td' n) ∘ ch (suc n) (psn+1<ssm⇒sn≤ssm pn+1<m) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (invrewrite-type ∘ mapB g ∘ up (s≤s z≤n) sn≤m ∘ rewrite-type) w) (lemma1HEQ (x ∷ xs) (psn+1<ssm⇒sn≤ssm pn+1<m) (ssn≤ssm⇒pn+1<ssm sn≤m) 1≤m) ⟩
    (invrewrite-type ∘ mapB g ∘ up (s≤s z≤n) sn≤m ∘ rewrite-type ∘ repeatUp' n  ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ remove-invrewrite-type (mapB g(up (s≤s z≤n) sn≤m (rewrite-type  (repeatUp' n ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m)   (mapB ex (ch 1 1≤m (map f (x ∷ xs)))))))) ⟩ -- remove invrewrite-type
    (mapB g ∘ up (s≤s z≤n) sn≤m ∘ rewrite-type ∘ repeatUp' n  ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ mapB-up-eq ((rewrite-type ∘ repeatUp' n  ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs)) ((repeatUp' n ≤-refl (tt2 n pn+1<m) ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs)) (s≤s z≤n) sn≤m (tt1 ≤-refl) pn+1<m (HEq.≡-to-≅ (sym (n+1≡sucn n))) HEq.refl helperlem1 ⟩ -- 
    (mapB g ∘ up (tt1 ≤-refl) (pn+1<m)  ∘ repeatUp' n ≤-refl (tt2 n pn+1<m) ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs) 
  HEq.≅-Reasoning.≅⟨ HEq.refl ⟩ -- def. of repeatUp'
    (repeatUp' (suc n) ≤-refl pn+1<m ∘ mapB ex ∘ ch 1 1≤m ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.∎
  where 
    helperlem1 : rewrite-type (repeatUp' n ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))) HEq.≅ repeatUp' n ≤-refl (tt2 n pn+1<m) (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))
    helperlem1 = 
      HEq.≅-Reasoning.begin 
        rewrite-type (repeatUp' n ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m)  (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs)))))
      HEq.≅-Reasoning.≅⟨ remove-rewrite-type (repeatUp' n ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))) ⟩ 
        repeatUp' n ≤-refl (ssn≤ssm⇒pn+1<ssm sn≤m) (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))
      HEq.≅-Reasoning.≅⟨ HEq.cong(λ w → repeatUp' n ≤-refl w (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))) (HEq.≡-to-≅ (≤-irrelevant (ssn≤ssm⇒pn+1<ssm sn≤m) (tt2 n pn+1<m))) ⟩ 
        repeatUp' n ≤-refl (tt2 n pn+1<m) (N (T0 (f x)) (mapB ex (ch 1 (s≤s z≤n) (map f xs))))
      HEq.≅-Reasoning.∎


lemma4 : {n : ℕ} → (xs : Vec X (suc (suc n))) → td (suc n) xs ≡ (td' (suc n) ∘ map f) xs
lemma4 {zero} (x ∷ y ∷ []) = refl
lemma4 {suc n} (x ∷ xs@(y ∷ ys@(z ∷ zs))) = 
  begin 
    td (suc (suc n)) (x ∷ xs)
  ≡⟨ refl ⟩ 
    (g ∘ map (td (suc n)) ∘ subs) (x ∷ xs)
  ≡⟨ cong (λ w → (g ∘ map w ∘ subs) (x ∷ xs)) helperlem1 ⟩
    (g ∘ map (td' (suc n) ∘ map f) ∘ subs) (x ∷ xs)
  ≡⟨ cong (λ w → g w) (map-compose (td' (suc n)) (map f) (subs (x ∷ xs))) ⟩ -- map f.g = map f . map g
    (g ∘ map (td' (suc n)) ∘ map (map f) ∘ subs) (x ∷ xs)
  ≡⟨ cong (λ w → (g ∘ map (td' (suc n))) w ) (subs-natural (suc (suc n)) (x ∷ xs)) ⟩ -- map (map f) ∘ subs = subs ∘ map f
    (g ∘ map (td' (suc n)) ∘ subs ∘ map f)  (x ∷ xs) 
  ≡⟨ refl ⟩ -- def. of td'
    (td' (suc (suc n)) ∘ map f) (x ∷ xs)
  ∎ 
  where 
    helperlem1 : td (suc n) ≡ td' (suc n) ∘ map f
    helperlem1 = funext (λ x₁ → lemma4 x₁)

-- map . subs  = unT . up . mapB . ch 
-- subs xs = unT up ch n $ xs .
lemma5 : (n : ℕ) → (0<n : 0 < n) ( 0<1+n : n < suc n) → (xs : Vec Y (suc n)) → subs xs ≡ (unTn ∘ up 0<n  0<1+n ∘ ch n (n≤1+n n)) xs
lemma5 (suc zero) 0<n  0<1+n (x ∷ y ∷ []) = refl
lemma5 (suc (suc n)) 0<n  0<1+n (x ∷ xs@(y ∷ ys@(z ∷ zs))) = 
  begin 
    subs (x ∷ xs)
  ≡⟨ refl ⟩ -- def. of subs
    snoc (map (x ∷_) (subs xs)) xs
  -- ≡⟨ cong (λ w → snoc w xs) (helperlem3 (suc n) (s≤s z≤n) x xs) ⟩
  ≡⟨ cong (λ w → snoc w xs) (helperlem3 n x xs) ⟩
    snoc (unTn (up (s≤s z≤n) (≤-refl) t)) xs
  ≡⟨ refl ⟩ -- unTn ∘ Tn = id
    unTn {n = n} (Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) t)) xs))
  ≡⟨ cong (λ w → unTn w) helperlem2 ⟩
    (unTn ∘ up 0<n  0<1+n) (N t (Tn xs))
  ≡⟨ refl ⟩
    (unTn ∘ up 0<n  0<1+n) (N (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ (n≤1+n (suc (suc n)))) xs)) (Tn xs))
  ≡⟨ cong(λ w → (unTn ∘ up 0<n  0<1+n) (N (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ (n≤1+n (suc (suc n)))) xs)) w)) (sym (lemma-ch-eq-Tn (suc n) (lemma3 (n≤1+n (suc (suc n))) ssn≠sssn) (y ∷ z ∷ zs))) ⟩
    (unTn ∘ up 0<n  0<1+n) (N (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ (n≤1+n (suc (suc n)))) xs)) (ch (suc (suc n)) (lemma3 (n≤1+n (suc (suc n))) ssn≠sssn) xs))
  ≡⟨ cong (λ w → (unTn ∘ up 0<n  0<1+n) w) (sym (lemma-ch-neq-rec (n≤1+n (suc (suc n))) ssn≠sssn x xs)) ⟩
    (unTn ∘ up 0<n  0<1+n ∘ ch (suc (suc n)) (n≤1+n (suc (suc n)))) (x ∷ xs)
  ∎ 
  where  -- B (Vec X (suc (suc n))) (suc n) (suc (suc n))
    t = (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ (n≤1+n (suc (suc n)))) xs))
    helperlem1 : Σ[ t ∈ B (Vec Y (suc (suc n))) n (suc n)] Σ[ u ∈ B (Vec Y (suc (suc n))) (suc n) (suc n)]   (mapB (x ∷_) (ch (suc n) (s≤s⁻¹ (n≤1+n (suc (suc n)))) xs) ≡ N t u)
    helperlem1 with suc n ≟ suc (suc n)
    ... | yes ()
    ... | no p with suc n ≟ suc n
    ... | no q = ⊥-elim (q refl)
    ... | yes refl = ((mapB (_∷_ x) (mapB (_∷_ y) (ch n (≤-step (≤-reflexive refl)) (z ∷ zs)))) , (Tn (x ∷ z ∷ zs)), refl) 
    helperlem2 : Tn (snoc (unTn (up (s≤s z≤n) (≤-refl) t)) xs) ≡  (up 0<n  0<1+n) (N t (Tn xs))
    helperlem2 with helperlem1 
    ... | (t' , u , eq)
      rewrite eq = refl

    helperlem3 : (n : ℕ) → (x : Y) → (xs : Vec Y (suc (suc n))) → map (x ∷_) (subs xs) ≡ unTn (up (s≤s z≤n) ≤-refl (mapB (x ∷_) (ch (suc n) (n≤1+n (suc n)) xs)))
    helperlem3 zero x (x₁ ∷ y ∷ []) = refl
    helperlem3 (suc zero) x xs@(y ∷ ys@(z ∷ zs@(r ∷ []))) = refl
    helperlem3 (suc (suc n)) x xs@(y ∷ ys@(z ∷ zs@(r ∷ rs@(t ∷ ts)))) = 
      begin 
        map (_∷_ x) (subs xs)
      ≡⟨ refl ⟩
        unTn {n = n} (Tn (map (_∷_ x) (subs xs)))
      ≡⟨ refl ⟩ -- def. of mapB
        unTn {n = n} (mapB (map (_∷_ x)) (Tn (subs xs)))
      ≡⟨ refl ⟩ -- def. of mapB
        unTn {n = n} (mapB (map (_∷_ x)) (mapB subs (Tn xs))) 
      ≡⟨ cong (λ w → unTn (mapB (map (_∷_ x)) (mapB subs w))) (sym (lemma-ch-eq-Tn (suc (suc (suc n))) ≤-refl xs)) ⟩ 
        unTn (mapB (map (_∷_ x)) (mapB subs (ch (suc (suc (suc (suc n)))) ≤-refl xs)))
      ≡⟨ cong (λ w → unTn (mapB (map (_∷_ x)) w)) (sym (thm1' (s≤s z≤n) ≤-refl (n≤1+n (suc (suc (suc n)))) ≤-refl xs)) ⟩ 
        unTn(mapB (map (_∷_ x)) (up (s≤s z≤n) ≤-refl  (ch (suc (suc (suc n))) (n≤1+n (suc (suc (suc n))))  xs)))
      ≡⟨ cong (λ w → unTn w) (sym (up-natural (x ∷_) (s≤s z≤n) ≤-refl (ch (suc (suc (suc n))) (n≤1+n (suc (suc (suc n))))  xs))) ⟩
        unTn (up (s≤s z≤n) ≤-refl (mapB (x ∷_) (ch (suc (suc (suc n))) (n≤1+n (suc (suc (suc n)))) xs)))
      ∎

-- lemma6HEQ : {n : ℕ} → (xs : Vec X (suc n)) → td (suc n) xs  HEq.≅ (unTn ∘ mapB g ∘ up (?) (?) ∘ mapB (td' n) ∘ ch (suc n) (?) ∘ map f ) xs 
lemma6HEQ : {n : ℕ} → (xs : Vec X (suc (suc n))) → td (suc n) xs HEq.≅ (unTn ∘ mapB g ∘ up (s≤s z≤n) (≤-refl) ∘ mapB (td' n) ∘ ch (suc n) (n≤1+n (suc n)) ∘ map f) xs
lemma6HEQ {zero} (x ∷ y ∷ []) = HEq.refl
lemma6HEQ {suc n} (x ∷ xs@(y ∷ ys@(z ∷ zs))) =
  HEq.≅-Reasoning.begin 
    td (suc (suc n)) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.≡-to-≅ (lemma4 ((x ∷ xs))) ⟩ -- lemma4
    (td' (suc (suc n)) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.refl ⟩ -- def. of td'
    (g ∘ map (td' (suc n)) ∘ subs ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (g ∘ map (td' (suc n))) w) (HEq.≡-to-≅ (lemma5 (suc (suc n)) (s≤s z≤n) ≤-refl (f x ∷ f y ∷ map f ys))) ⟩ -- lemma5 
    (g ∘ map (td' (suc n)) ∘ unTn ∘ up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.≡-to-≅ (unTn-natural (g ∘ map (td' (suc n))) ((up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs))) ⟩ -- naturality of unT
    (unTn ∘ mapB (g ∘ map (td' (suc n))) ∘ up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → unTn w) (HEq.≡-to-≅ (mapB-compose g (map (td' (suc n))) ((up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs)))) ⟩ -- mapB (g . f) = mapB g . mapB f
    (unTn ∘ mapB g ∘ mapB (map (td' (suc n))) ∘ up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (unTn ∘ mapB g) w) (HEq.≡-to-≅ helperlem1) ⟩ 
    (unTn ∘ mapB g ∘ up (s≤s z≤n) ≤-refl ∘ mapB (td' (suc n)) ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f)(x ∷ xs)
  HEq.≅-Reasoning.∎ 
  where  
    helperlem1 : (mapB (map (td' (suc n))) ∘ up (s≤s z≤n) ≤-refl ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs) ≡ (up (s≤s z≤n) ≤-refl ∘ mapB (td' (suc n)) ∘ ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f)(x ∷ xs)
    helperlem1 rewrite (sym (up-natural (td' (suc n)) (s≤s z≤n) ≤-refl ((ch (suc (suc n)) (n≤1+n (suc (suc n))) ∘ map f) (x ∷ xs)))) = refl

firstpart-helper : {n : ℕ} →(t : B Y (suc n) (suc (suc n))) → (mapB g ∘ up (s≤s z≤n) (≤-refl)) t HEq.≅ (rewrite-type {n = suc n}∘ (mapB g ∘ up (tt1 (≤-refl)) (psn+1<ssn {n = n})) ∘ invrewrite-type) t
firstpart-helper {n} t =
  HEq.≅-Reasoning.begin
    (mapB g ∘ up (s≤s z≤n) ≤-refl) t 
  HEq.≅-Reasoning.≅⟨  mapB-up-eq t (invrewrite-type t) (s≤s z≤n) (≤-refl) (tt1 ≤-refl) (psn+1<ssn) (HEq.≡-to-≅ (sym (n+1≡sucn n))) HEq.refl (HEq.sym (remove-invrewrite-type t)) ⟩
    (mapB g ∘ up (tt1 ≤-refl) psn+1<ssn ∘ invrewrite-type) t 
  HEq.≅-Reasoning.≅⟨ HEq.sym (remove-rewrite-type (mapB g (up (tt1 ≤-refl) psn+1<ssn (invrewrite-type t)))) ⟩ 
    (rewrite-type ∘ mapB g ∘ up (tt1 ≤-refl) psn+1<ssn ∘ invrewrite-type) t
  HEq.≅-Reasoning.∎  


firstpart : {n : ℕ} →(t : B Y (suc n) (suc (suc n))) → (unTn ∘ mapB g ∘ up (s≤s z≤n) (≤-refl)) t HEq.≅ (unTn ∘ rewrite-type ∘ (mapB g ∘ up (tt1 (≤-refl)) (psn+1<ssn {n = n})) ∘ invrewrite-type) t
firstpart {n} t = HEq.cong (λ w → unTn w) ((firstpart-helper t))

thm2' : (n : ℕ) → (xs : Vec X (suc n)) → td n xs HEq.≅ bu n xs
thm2' zero (x ∷ []) = HEq.refl
thm2' (suc n) (x ∷ xs@(y ∷ ys)) = 
  HEq.≅-Reasoning.begin
    td (suc n) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ lemma6HEQ (x ∷ xs) ⟩
    (unTn ∘ mapB g ∘ up (s≤s z≤n) (≤-refl) ∘ mapB (td' n) ∘ ch (suc n) (n≤1+n (suc n)) ∘ map f) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ firstpart ((mapB (td' n) ∘ ch (suc n) (n≤1+n (suc n)) ∘ map f) (x ∷ xs))  ⟩
    (unTn ∘ rewrite-type ∘ (mapB g ∘ up (tt1 (≤-refl)) (psn+1<ssn {n = n})) ∘ invrewrite-type ∘ mapB (td' n) ∘ ch (suc n) (n≤1+n (suc n)) ∘ map f) (x ∷ xs) 
  HEq.≅-Reasoning.≅⟨ HEq.cong (λ w → (unTn ∘ rewrite-type ∘ (mapB g ∘ up (tt1 ≤-refl) (psn+1<ssn {n = n}))) w ) (lemma1HEQ (x ∷ xs) (n≤1+n (suc n)) (tt2 n psn+1<ssn) (s≤s z≤n))  ⟩ 
    (unTn ∘ rewrite-type ∘ (mapB g ∘ up (tt1 (≤-refl)) (psn+1<ssn {n = n}) ) ∘ repeatUp' n  (≤-refl) (tt2 n (psn+1<ssn {n = n})) ∘ mapB ex ∘ ch 1 (s≤s z≤n) ∘ (map f) ) (x ∷ xs)
  HEq.≅-Reasoning.≅⟨ HEq.refl ⟩
    (unTn ∘ rewrite-type ∘ repeatUp' (suc n) (≤-refl) (psn+1<ssn {n = n}) ∘ mapB ex ∘ ch 1 ( s≤s z≤n) ∘ (map f) ) (x ∷ xs) 
  HEq.≅-Reasoning.≅⟨ HEq.refl ⟩ 
    bu (suc n) (x ∷ y ∷ ys)
  HEq.≅-Reasoning.∎     
  
thm2 :  (n : ℕ) → (xs : Vec X (suc n)) → td n xs ≡ bu n xs
thm2 n xs = HEq.≅-to-≡ (thm2' n xs)
                