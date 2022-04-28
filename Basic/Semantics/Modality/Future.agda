--------------------------------------------------------------------
-- Semantics of the future modality `[ t ] A` as a graded comonad --
--                                                                --
-- While `[ t ] A` is in fact a strong monoidal functor in this   --
-- concrete semantics, then analogously to the context modality   --
-- we only ever use the graded comonad (with invertible counit)   --
-- structure of it when interpreting the language in general.     --
--------------------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product renaming (map to mapˣ)
open import Data.Sum renaming (map to map⁺)
open import Data.Unit hiding (_≤_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Syntax.Language

open import Semantics.TSets

open import Util.Time

module Semantics.Modality.Future where

-- STRUCTURE

-- Functor

[_]ᵒ : Time → TSet → TSet
[ τ ]ᵒ A =
  tset
    (λ t' → carrier A (t' + τ))
    (λ p x → monotone A (+-mono-≤ p ≤-refl) x)
    (λ x → trans
             (cong (λ p → monotone A p x) (≤-irrelevant _ ≤-refl))
             (monotone-refl A x))
    (λ p q x → trans
                 (monotone-trans A _ _ x)
                 (cong
                   (λ r → monotone A r x)
                   (≤-irrelevant _ (+-mono-≤ (≤-trans p q) ≤-refl))))

[_]ᶠ : ∀ {A B} → (τ : Time) → A →ᵗ B → [ τ ]ᵒ A →ᵗ [ τ ]ᵒ B
[ τ ]ᶠ f =
  tset-map
    (map-carrier f)
    (λ p x → map-nat f (+-mono-≤ p ≤-refl) x)

-- Monotonicity for gradings

[]-≤ : ∀ {A τ₁ τ₂} → τ₁ ≤ τ₂ → [ τ₁ ]ᵒ A →ᵗ [ τ₂ ]ᵒ A
[]-≤ {A} p =
  tset-map
    (λ x → monotone A (+-mono-≤ ≤-refl p) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Counit

ε : ∀ {A} → [ 0 ]ᵒ A →ᵗ A
ε {A} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (+-identityʳ t)) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

ε⁻¹ : ∀ {A} → A →ᵗ [ 0 ]ᵒ A
ε⁻¹ {A} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (sym (+-identityʳ t))) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Comultiplication

δ : ∀ {A τ₁ τ₂} → [ τ₁ + τ₂ ]ᵒ A →ᵗ [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A)
δ {A} {τ₁} {τ₂} =
  tset-map
    (λ {t} x → monotone A (≤-reflexive (sym (+-assoc t τ₁ τ₂))) x)
    (λ p x →
      trans
        (monotone-trans A _ _ x)
        (trans
          (cong (λ q → monotone A q x) (≤-irrelevant _ _))
          (sym (monotone-trans A _ _ x))))

-- Derived general unit map (a value now is
-- also available in at most τ time steps)

η-[] : ∀ {A τ} → A →ᵗ [ τ ]ᵒ A
η-[] {A} {τ} = []-≤ {A = A} z≤n ∘ᵗ ε⁻¹


-- PROPERTIES

-- [_] is functorial

abstract
  []-id : ∀ {A τ} → [ τ ]ᶠ (idᵗ {A = A}) ≡ᵗ idᵗ
  []-id = eqᵗ (λ {t} x →
    trans (idᵗ-reveal _) (sym (idᵗ-reveal _)))

  []-∘ : ∀ {A B C τ} → (f : A →ᵗ B) → (g : B →ᵗ C)
       → [ τ ]ᶠ (g ∘ᵗ f) ≡ᵗ [ τ ]ᶠ g ∘ᵗ [ τ ]ᶠ f
  []-∘ {τ = τ} f g = eqᵗ (λ {t} x →
    trans
      (∘ᵗ-reveal _ _ _)
      (sym (∘ᵗ-reveal _ _ _)))

-- []-≤ is natural

abstract
  []-≤-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B) → (p : τ₁ ≤ τ₂)
           → [ τ₂ ]ᶠ f ∘ᵗ []-≤ {A = A} p ≡ᵗ []-≤ {A = B} p ∘ᵗ [ τ₁ ]ᶠ f
  []-≤-nat {A} {B} {τ₁ = τ₁} {τ₂ = τ₂} f p = eqᵗ (λ {t} x →
    trans
      (∘ᵗ-reveal _ _ _)
      (trans
        (map-nat f (+-mono-≤ (≤-reflexive refl) p) x)
        (sym (∘ᵗ-reveal _ _ _))))

-- [_] is functorial in the gradings

abstract
  []-≤-refl : ∀ {A τ} → []-≤ {A} (≤-refl {τ}) ≡ᵗ idᵗ
  []-≤-refl {A} =
    eqᵗ (λ {t} x →
      trans
        (cong (λ p → monotone A p x) (≤-irrelevant _ _))
        (trans
          (monotone-refl A x)
          (sym (idᵗ-reveal _))))

  []-≤-trans : ∀ {A τ τ' τ''} → (p : τ ≤ τ') → (q : τ' ≤ τ'')
             → []-≤ {A} q ∘ᵗ []-≤ {A} p ≡ᵗ []-≤ {A} (≤-trans p q)
  []-≤-trans {A} p q =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (monotone-trans A _ _ x)
          (cong (λ r → monotone A r x) (≤-irrelevant _ _))))

-- ε and ε⁻¹ are natural

abstract
  []-ε-nat : ∀ {A B} → (f : A →ᵗ B)
           → f ∘ᵗ ε ≡ᵗ ε ∘ᵗ [ 0 ]ᶠ f
  []-ε-nat f =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (map-nat f (≤-reflexive (+-identityʳ t)) x)
          (sym (∘ᵗ-reveal _ _ _))))

  []-ε⁻¹-nat : ∀ {A B} → (f : A →ᵗ B)
             → [ 0 ]ᶠ f ∘ᵗ ε⁻¹ ≡ᵗ ε⁻¹ ∘ᵗ f
  []-ε⁻¹-nat f =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (map-nat f (≤-reflexive (sym (+-identityʳ t))) x)
          (sym (∘ᵗ-reveal _ _ _))))

-- δ is natural

abstract
  []-δ-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
           → [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f) ∘ᵗ δ {A} ≡ᵗ δ {B} ∘ᵗ [ τ₁ + τ₂ ]ᶠ f
  []-δ-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (map-nat f (≤-reflexive (sym (+-assoc t τ₁ τ₂))) x)
          (sym (∘ᵗ-reveal _ _ _))))

  []-δ-≤ : ∀ {A τ₁ τ₂ τ₁' τ₂'} → (p : τ₁ ≤ τ₁') → (q : τ₂ ≤ τ₂')
         → [ τ₁' ]ᶠ ([]-≤ {A} q) ∘ᵗ []-≤ {[ τ₂ ]ᵒ A} p ∘ᵗ δ {A = A}
         ≡ᵗ δ {A} ∘ᵗ []-≤ {A} (+-mono-≤ p q)
  []-δ-≤ {A} {τ₁' = τ₁'} p q =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (cong (map-carrier ([ τ₁' ]ᶠ ([]-≤ {A} q))) (∘ᵗ-reveal _ _ _))
            (trans
              (monotone-trans A _ _ _)
              (trans
                (monotone-trans A _ _ _)
                (trans
                  (cong (λ r → monotone A r x) (≤-irrelevant _ _))
                  (sym (monotone-trans A _ _ _))))))
          (sym (∘ᵗ-reveal _ _ _))))

-- ε is invertible

abstract
  []-ε∘ε⁻¹≡id : ∀ {A} → ε {A} ∘ᵗ ε⁻¹ ≡ᵗ idᵗ
  []-ε∘ε⁻¹≡id {A} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ p → monotone A p x) (≤-irrelevant _ _))
              (monotone-refl A x)))
          (sym (idᵗ-reveal _))))

  []-ε⁻¹∘ε≡id : ∀ {A} → ε⁻¹ {A} ∘ᵗ ε ≡ᵗ idᵗ
  []-ε⁻¹∘ε≡id {A} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ p → monotone A p x) (≤-irrelevant _ _))
              (monotone-refl A x)))
          (sym (idᵗ-reveal _))))

-- Graded comonad laws

abstract
  []-ε∘δ≡id : ∀ {A τ} → ε ∘ᵗ δ {A} {0} {τ} ≡ᵗ idᵗ
  []-ε∘δ≡id {A} {τ} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ p → monotone A p x) (≤-irrelevant _ _))
              (monotone-refl A x)))
          (sym (idᵗ-reveal _))))

  []-Dε∘δ≡≤ : ∀ {A τ}
            → [ τ ]ᶠ (ε {A}) ∘ᵗ δ {A} {τ} {0}
            ≡ᵗ []-≤ {A} (≤-reflexive (+-identityʳ τ))
  []-Dε∘δ≡≤ {A} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (monotone-trans A _ _ x)
          (cong (λ p → monotone A p x) (≤-irrelevant _ _))))

  []-δ∘δ≡Dδ∘δ∘≤ : ∀ {A τ₁ τ₂ τ₃}
                → δ {[ τ₃ ]ᵒ A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁ + τ₂} {τ₃}
                ≡ᵗ    [ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}) ∘ᵗ δ {A} {τ₁} {τ₂ + τ₃}
                   ∘ᵗ []-≤ {A} (≤-reflexive (+-assoc τ₁ τ₂ τ₃))
  []-δ∘δ≡Dδ∘δ∘≤ {A} {τ₁} {τ₂} {τ₃} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (trans
              (monotone-trans A _ _ x)
              (trans
                (trans
                  (cong (λ p → monotone A p x) (≤-irrelevant _ _))
                  (sym (monotone-trans A _ _ _)))
                (sym (monotone-trans A _ _ _))))
            (sym (cong (map-carrier ([ τ₁ ]ᶠ (δ {A} {τ₂} {τ₃}))) (∘ᵗ-reveal _ _ _))))
          (sym (∘ᵗ-reveal _ _ _))))

-- In this concrete semantics, ⟨_⟩ is in fact strong monoidal

abstract
  δ⁻¹ : ∀ {A τ₁ τ₂} → [ τ₁ ]ᵒ ([ τ₂ ]ᵒ A) →ᵗ [ τ₁ + τ₂ ]ᵒ A
  δ⁻¹ {A} {τ₁} {τ₂} =
    tset-map
      (λ {t} x → monotone A (≤-reflexive (+-assoc t τ₁ τ₂)) x)
      (λ p x →
        trans
          (monotone-trans A _ _ x)
          (trans
            (cong (λ q → monotone A q x) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ x))))

  []-δ⁻¹-nat : ∀ {A B τ₁ τ₂} → (f : A →ᵗ B)
             → [ τ₁ + τ₂ ]ᶠ f ∘ᵗ δ⁻¹ {A} ≡ᵗ δ⁻¹ {B} ∘ᵗ [ τ₁ ]ᶠ ([ τ₂ ]ᶠ f)
  []-δ⁻¹-nat {τ₁ = τ₁} {τ₂ = τ₂} f =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (map-nat f (≤-reflexive (+-assoc t τ₁ τ₂)) x)
          (sym (∘ᵗ-reveal _ _ _))))

  []-δ∘δ⁻¹≡id : ∀ {A τ₁ τ₂} → δ {A} {τ₁} {τ₂} ∘ᵗ δ⁻¹ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
  []-δ∘δ⁻¹≡id {A} {τ₁} {τ₂} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ p → monotone A p x) (≤-irrelevant _ _))
              (monotone-refl A x)))
          (sym (idᵗ-reveal _))))

  []-δ⁻¹∘δ≡id : ∀ {A τ₁ τ₂} → δ⁻¹ {A} {τ₁} {τ₂} ∘ᵗ δ {A} {τ₁} {τ₂} ≡ᵗ idᵗ
  []-δ⁻¹∘δ≡id {A} {τ₁} {τ₂} =
    eqᵗ (λ {t} x →
      trans
        (∘ᵗ-reveal _ _ _)
        (trans
          (trans
            (monotone-trans A _ _ x)
            (trans
              (cong (λ p → monotone A p x) (≤-irrelevant _ _))
              (monotone-refl A x)))
          (sym (idᵗ-reveal _))))
