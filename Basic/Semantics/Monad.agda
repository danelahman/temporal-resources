---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

-- Note: A version of the monad that is not quotioned by
--       the delay equations (identity and composition)

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Monad.Core renaming (⟦_⟧ᵍ to ⟦_⟧ᵍ'; Tᵒ to Tᵒ'; Tᶠ to Tᶠ'; ηᵀ to ηᵀ'; μᵀ to μᵀ';
                                           Tᶠ-idᵗ to Tᶠ-idᵗ'; Tᶠ-∘ᵗ to Tᶠ-∘ᵗ'; τ-substᵀ to τ-substᵀ';
                                           ηᵀ-nat to ηᵀ-nat'; μᵀ-nat to μᵀ-nat';
                                           μᵀ-identity₁ to μᵀ-identity₁'; μᵀ-identity₂ to μᵀ-identity₂';
                                           μᵀ-assoc to μᵀ-assoc')
open import Semantics.Monad.Strength renaming (strᵀ to strᵀ'; strᵀ-nat to strᵀ-nat')
open import Semantics.Monad.Effects renaming (delayᵀ to delayᵀ'; opᵀ to opᵀ')
open import Semantics.Monad.Handling renaming (T-alg-of-handlerᵀ to T-alg-of-handlerᵀ')

open import Util.HProp
open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad where

-- The free graded monad generated by the operations in Op
----------------------------------------------------------

-- Interpretation of ground types
---------------------------------

⟦_⟧ᵍ : GType → TSet
⟦_⟧ᵍ = ⟦_⟧ᵍ'


-- Abstractly (re-)exposing the top-level monad structure, operations, and laws

---- Monad structure

abstract

  Tᵒ : TSet → Time → TSet
  Tᵒ = Tᵒ'
 
  Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ
  Tᶠ = Tᶠ'

  ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0
  ηᵀ = ηᵀ'

  μᵀ : ∀ {A τ τ'} → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')
  μᵀ = μᵀ'

  Tᶠ-idᵗ : ∀ {A τ}
         → Tᶠ {A} {A} {τ} idᵗ ≡ᵗ idᵗ
  Tᶠ-idᵗ = Tᶠ-idᵗ'

  Tᶠ-∘ᵗ : ∀ {A B C τ}
        → (g : B →ᵗ C)
        → (f : A →ᵗ B)
        → Tᶠ {A} {C} {τ} (g ∘ᵗ f) ≡ᵗ Tᶠ g ∘ᵗ Tᶠ f
  Tᶠ-∘ᵗ = Tᶠ-∘ᵗ'

  τ-substᵀ : ∀ {A τ τ'}
           → τ ≡ τ'
           → Tᵒ A τ →ᵗ Tᵒ A τ'
  τ-substᵀ = τ-substᵀ'

  ηᵀ-nat : ∀ {A B}
         → (f : A →ᵗ B)
         → ηᵀ ∘ᵗ f ≡ᵗ Tᶠ f ∘ᵗ ηᵀ
  ηᵀ-nat = ηᵀ-nat'

  μᵀ-nat : ∀ {A B τ τ'}
         → (f : A →ᵗ B)
         → μᵀ {τ = τ} {τ' = τ'} ∘ᵗ Tᶠ (Tᶠ f) ≡ᵗ Tᶠ f ∘ᵗ μᵀ
  μᵀ-nat = μᵀ-nat'

  μᵀ-identity₁ : ∀ {A τ}
               →  μᵀ {τ = 0} {τ' = τ} ∘ᵗ ηᵀ {Tᵒ A τ} ≡ᵗ idᵗ
  μᵀ-identity₁ = μᵀ-identity₁'

  μᵀ-identity₂ : ∀ {A τ}
               →  μᵀ {τ = τ} {τ' = 0} ∘ᵗ Tᶠ (ηᵀ {A})
               ≡ᵗ τ-substᵀ (sym (+-identityʳ τ))
  μᵀ-identity₂ = μᵀ-identity₂'

  μᵀ-assoc : ∀ {A τ τ' τ''}
           →  μᵀ {A} {τ} {τ' + τ''} ∘ᵗ Tᶠ μᵀ
           ≡ᵗ τ-substᵀ (+-assoc τ τ' τ'') ∘ᵗ (μᵀ ∘ᵗ μᵀ)
  μᵀ-assoc = μᵀ-assoc'


---- Strength

abstract

  strᵀ : ∀ {A B τ τ'} → [ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ →ᵗ Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ
  strᵀ {A} {B} {τ} {τ'} = strᵀ' {A} {B} {τ} {τ'}

  strᵀ-nat : ∀ {A A' B B' τ τ'}
            → (f : A →ᵗ A')
            → (g : B →ᵗ B')
            →  strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ (⟨ τ' ⟩ᶠ f)) (Tᶠ g)
            ≡ᵗ Tᶠ (mapˣᵗ (⟨ τ' ⟩ᶠ f) g) ∘ᵗ strᵀ {A} {B}
  strᵀ-nat = strᵀ-nat'


---- Effects

abstract

  delayᵀ : ∀ {A} (τ : Time) {τ'}
         → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')
  delayᵀ = delayᵀ'

  opᵀ : ∀ {A τ} → (op : Op)
      → ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ) →ᵗ Tᵒ A (op-time op + τ)
  opᵀ = opᵀ'


---- Effect handling

abstract

  T-alg-of-handlerᵀ : ∀ {A τ τ'}
                    → Π Op (λ op → Π Time (λ τ'' →
                       ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                         ⇒ᵗ Tᵒ A (op-time op + τ'')))
                    →ᵗ Tᵒ (Tᵒ A τ') τ ⇒ᵗ Tᵒ A (τ + τ')
  T-alg-of-handlerᵀ = T-alg-of-handlerᵀ'

