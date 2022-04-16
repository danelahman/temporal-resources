--------------------------------------------------------
-- Time-varying sets (covariant presheaves on (ℕ,≤)), --
-- their morphisms, and basic categorical structures  --
--------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding (Extensionality)
open Eq.≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)

open import Util.Time

module Semantics.TSets where

postulate
  fun-ext  : ∀ {a b} → Extensionality a b            -- assuming function extensionality
  ifun-ext : ∀ {a b} → ExtensionalityImplicit a b   -- and the same for functions with implicit arguments

-- Some auxiliary lemmas concerning minus on natural numbers

n∸m∸k≡n∸m+k : (n m k : ℕ) → n ∸ m ∸ k ≡ n ∸ (m + k)
n∸m∸k≡n∸m+k zero    zero    k       = refl
n∸m∸k≡n∸m+k zero    (suc m) zero    = refl
n∸m∸k≡n∸m+k zero    (suc m) (suc k) = refl
n∸m∸k≡n∸m+k (suc n) zero    k       = refl
n∸m∸k≡n∸m+k (suc n) (suc m) k       = n∸m∸k≡n∸m+k n m k

n≤k⇒m≤k∸n⇒n+m≤k : (n m k : ℕ) → n ≤ k → m ≤ k ∸ n → n + m ≤ k
n≤k⇒m≤k∸n⇒n+m≤k zero m k z≤n q = q
n≤k⇒m≤k∸n⇒n+m≤k (suc n) m (suc k) (s≤s p) q =
  +-monoʳ-≤ 1 (n≤k⇒m≤k∸n⇒n+m≤k n m k p q)

n≤m⇒m∸n+n≤m : (n m : ℕ) → n ≤ m → m ∸ n + n ≤ m
n≤m⇒m∸n+n≤m zero m z≤n =
  ≤-reflexive (+-identityʳ m)
n≤m⇒m∸n+n≤m (suc n) (suc m) (s≤s p) =
  ≤-trans
    (≤-reflexive (+-suc (m ∸ n) n))
    (+-monoʳ-≤ 1 (n≤m⇒m∸n+n≤m n m p))

n+m≤k⇒m≤k∸n : (n m k : ℕ) → n + m ≤ k → m ≤ k ∸ n
n+m≤k⇒m≤k∸n zero    m       k       p       = p
n+m≤k⇒m≤k∸n (suc n) zero    k       p       = z≤n
n+m≤k⇒m≤k∸n (suc n) (suc m) (suc k) (s≤s p) = n+m≤k⇒m≤k∸n n (suc m) k p

n≡m+k≤n' : ∀ {n n' m k} → n ≡ m + k → n ≤ n' → Σ[ m' ∈ ℕ ] (n' ≡ m' + k × m ≤ m')
n≡m+k≤n' {n' = n'} {m = m} p z≤n
  rewrite m+n≡0⇒m≡0 m (sym p) | m+n≡0⇒n≡0 m (sym p) =
    n' , sym (+-identityʳ n') , z≤n
n≡m+k≤n' {n' = .(suc _)} {m = zero} refl (s≤s {n''} {n'''} q) with n≡m+k≤n' {k = n''} refl q
... | p' , q' , r' = p' , trans (cong suc q') (sym (+-suc p' n'')) , r'
n≡m+k≤n' {n' = .(suc _)} {m = suc m} p (s≤s {n''} {n'''} q) with suc-injective p
... | s with n≡m+k≤n' {m = m} s q
... | p' , q' , r' = suc p' , cong suc q' , +-mono-≤ (≤-refl {1}) r'

-- Time-varying sets

record TSet : Set₁ where
  constructor
    tset
  field
    carrier  : Time → Set
    monotone : ∀ {t t'} → t ≤ t' → carrier t → carrier t'

    monotone-refl  : ∀ {t}
                   → (x : carrier t) → monotone (≤-refl {t}) x ≡ x
    monotone-trans : ∀ {t t' t''} → (p : t ≤ t') → (q : t' ≤ t'')
                   → (x : carrier t) → monotone q (monotone p x) ≡ monotone (≤-trans p q) x

open TSet public

-- Constant time-varying sets

ConstTSet : Set → TSet
ConstTSet A = tset (λ _ → A) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

-- Maps of time-varying sets

record _→ᵗ_ (A B : TSet) : Set where
  constructor
    tset-map
  field
    map-carrier : ∀ {t} → carrier A t → carrier B t

    -- TODO: also include naturality law

infix 20 _→ᵗ_

open _→ᵗ_ public

-- Equality of TSet-morphisms

_≡ᵗ_ : ∀ {A B} → A →ᵗ B → A →ᵗ B → Set
_≡ᵗ_ {A} f g = ∀ {t} → (x : carrier A t) → map-carrier f x ≡ map-carrier g x

infix 5 _≡ᵗ_

-- Identity and composition of maps

idᵗ : ∀ {A} → A →ᵗ A
idᵗ = tset-map id

_∘ᵗ_ : ∀ {A B C} → B →ᵗ C → A →ᵗ B → A →ᵗ C
g ∘ᵗ f = tset-map (map-carrier g ∘ map-carrier f)

infixr 9 _∘ᵗ_

-- Product, sum, exponent, etc structures

---- terminal object

𝟙ᵗ : TSet
𝟙ᵗ = tset (λ _ → ⊤) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

terminalᵗ : ∀ {A} → A →ᵗ 𝟙ᵗ
terminalᵗ = tset-map (λ _ → tt)

---- initial object

𝟘ᵗ : TSet
𝟘ᵗ = tset (λ _ → ⊥) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

initialᵗ : ∀ {A} → 𝟘ᵗ →ᵗ A
initialᵗ = tset-map (λ ())

---- products

_×ᵗ_ : TSet → TSet → TSet
A ×ᵗ B =
  tset
    (λ t → carrier A t × carrier B t)
    (λ p → mapˣ (monotone A p) (monotone B p))
    (λ x → cong₂ _,_ (monotone-refl A (proj₁ x)) (monotone-refl B (proj₂ x)))
    (λ p q x → cong₂ _,_ (monotone-trans A p q (proj₁ x)) (monotone-trans B p q (proj₂ x)))

infixr 23 _×ᵗ_

fstᵗ : ∀ {A B} → A ×ᵗ B →ᵗ A
fstᵗ = tset-map proj₁

sndᵗ : ∀ {A B} → A ×ᵗ B →ᵗ B
sndᵗ = tset-map proj₂

⟨_,_⟩ᵗ : ∀ {A B C} → A →ᵗ B → A →ᵗ C → A →ᵗ B ×ᵗ C
⟨ f , g ⟩ᵗ = tset-map < map-carrier f , map-carrier g >

mapˣᵗ : ∀ {A B C D} → A →ᵗ C → B →ᵗ D → A ×ᵗ B →ᵗ C ×ᵗ D
mapˣᵗ f g = tset-map (mapˣ (map-carrier f) (map-carrier g))

---- exponentials

_⇒ᵗ_ : TSet → TSet → TSet
A ⇒ᵗ B =
  tset
    (λ t → {t' : Time} → t ≤ t' → carrier A t' → carrier B t')
    (λ p f q a → f (≤-trans p q) a)
    (λ f → ifun-ext (fun-ext (λ p → fun-ext λ x →
             cong (λ p → f p x) (≤-irrelevant _ _))))
    (λ p q f → ifun-ext (fun-ext (λ r → fun-ext (λ x →
                 cong (λ p → f p x) (≤-irrelevant _ _)))))

infix 22 _⇒ᵗ_

appᵗ : ∀ {A B} → (A ⇒ᵗ B) ×ᵗ A →ᵗ B
appᵗ = tset-map λ { {t} (f , a) → f ≤-refl a }

curryᵗ : ∀ {A B C} → A ×ᵗ B →ᵗ C → A →ᵗ B ⇒ᵗ C
curryᵗ {A} f = tset-map (λ a → λ p b → map-carrier f (monotone A p a , b))

uncurryᵗ : ∀ {A B C} → A →ᵗ B ⇒ᵗ C → A ×ᵗ B →ᵗ C
uncurryᵗ f = tset-map λ { (a , b) → map-carrier f a ≤-refl b }

