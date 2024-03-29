------------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a strong monoidal    --
-- functor indexed by (ℕ,≤). It is the analogue of the comonadic      --
-- □-modality on types/formulae in Fitch-style modal lambda calculi.  --
--                                                                    --
-- Note: While `[ t ] A` is a strong monoidal functor, then below we  --
-- use the terminology (counit, comultiplication) of graded comonads. --
------------------------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Modality.Future (Cat : Category) where

open import Util.Equality
open import Util.Time

open Category Cat

record Future : Set₁ where

  field

    -- STRUCTURE

    -- Functor
    
    [_]ᵒ : Time → Obj → Obj
    [_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵐ B → [ τ ]ᵒ A →ᵐ [ τ ]ᵒ B
    
    -- Monotonicity for gradings

    []-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵐ [ τ₂ ]ᵒ A
  
    -- Counit and its inverse

    ε : ∀ {A} → [ 0 ]ᵒ A →ᵐ A
    ε⁻¹ : ∀ {A} → A →ᵐ [ 0 ]ᵒ A

    -- Comultiplication and its inverse
    
    δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵐ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
    δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵐ [ τ₁ + τ₂ ]ᵒ A

    -- PROPERTIES

    -- [_] is functorial

    []-idᵐ : ∀ {A τ} → [ τ ]ᶠ (idᵐ {A = A}) ≡ idᵐ
    []-∘ᵐ : ∀ {A B C τ} → (f : A →ᵐ B) → (g : B →ᵐ C)
          → [ τ ]ᶠ (g ∘ᵐ f) ≡ [ τ ]ᶠ g ∘ᵐ [ τ ]ᶠ f

    -- []-≤ is natural

    []-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B) → (p : τ₁ ≤ τ₂)
             → [ τ₂ ]ᶠ f ∘ᵐ []-≤ {A = A} p ≡ []-≤ {A = B} p ∘ᵐ [ τ₁ ]ᶠ f

    -- [_] is functorial in the gradings

    []-≤-refl : ∀ {A τ} → []-≤ {A} (≤-refl {τ}) ≡ idᵐ
    []-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
               → []-≤ {A} q ∘ᵐ []-≤ {A} p ≡ []-≤ {A} (≤-trans p q)

    -- ε and ε⁻¹ are natural

    []-ε-nat : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ ε ≡ ε ∘ᵐ [ 0 ]ᶠ f
    []-ε⁻¹-nat : ∀ {A B} → (f : A →ᵐ B) → [ 0 ]ᶠ f ∘ᵐ ε⁻¹ ≡ ε⁻¹ ∘ᵐ f

    -- δ and δ⁻¹ is natural

    []-δ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B)
             → [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f) ∘ᵐ δ {A} ≡ δ {B} ∘ᵐ [ τ₁ + τ₂ ]ᶠ f
    []-δ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵐ B)
               → [ τ₁ + τ₂ ]ᶠ f ∘ᵐ δ⁻¹ {A} ≡ δ⁻¹ {B} ∘ᵐ [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f)
    []-δ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
           → [ τ₁' ]ᶠ ([]-≤ {A} q) ∘ᵐ []-≤ {[ τ₂ ]ᵒ A} p ∘ᵐ δ {A = A} ≡ δ {A} ∘ᵐ []-≤ {A} (+-mono-≤ p q)

    -- ε is invertible

    []-ε∘ε⁻¹≡id : ∀ {A} → ε {A} ∘ᵐ ε⁻¹ ≡ idᵐ
    []-ε⁻¹∘ε≡id : ∀ {A} → ε⁻¹ {A} ∘ᵐ ε ≡ idᵐ

    -- δ is invertible

    []-δ∘δ⁻¹≡id : ∀ {A τ₁ τ₂} → δ {A} {τ₁} {τ₂} ∘ᵐ δ⁻¹ {A} {τ₁} {τ₂} ≡ idᵐ
    []-δ⁻¹∘δ≡id : ∀ {A τ₁ τ₂} → δ⁻¹ {A} {τ₁} {τ₂} ∘ᵐ δ {A} {τ₁} {τ₂} ≡ idᵐ

    -- Graded comonad laws

    []-ε∘δ≡id : ∀ {A τ} → ε ∘ᵐ δ {A} {0} {τ} ≡ idᵐ
    []-Dε∘δ≡id : ∀ {A τ} → [ τ ]ᶠ (ε {A}) ∘ᵐ δ {A} {τ} {0} ≡ []-≤ {A} (≤-reflexive (+-identityʳ τ))
    []-δ∘δ≡Dδ∘δ : ∀ {A τ₁ τ₂ τ₃}
                  → δ {[ τ₃ ]ᵒ A} {τ₁} {τ₂} ∘ᵐ δ {A} {τ₁ + τ₂} {τ₃}
                  ≡    [ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}) ∘ᵐ δ {A} {τ₁} {τ₂ + τ₃}
                    ∘ᵐ []-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃))
