-------------------------------------------------------
-- Model of the language based on time-varying sets  --
-------------------------------------------------------

module Semantics.Model.Examples.TSets.Model where

open import Semantics.Model

open import Semantics.Model.Examples.TSets.TSets

open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.Modality.Adjunction

open import Semantics.Model.Examples.TSets.BaseGroundTypes

open import Semantics.Model.Examples.TSets.Monad.Core

open import Util.Operations

TSetsModel : Model
TSetsModel = record {
  Cat = record
          { Obj              = TSet
          ; _→ᵐ_             = _→ᵗ_
          ; idᵐ              = idᵗ
          ; _∘ᵐ_             = _∘ᵗ_
          ; ∘ᵐ-identityˡ     = λ f → ≡ᵗ-≡ (∘ᵗ-identityˡ f)
          ; ∘ᵐ-identityʳ     = λ f → ≡ᵗ-≡ (∘ᵗ-identityʳ f)
          ; ∘ᵐ-assoc         = λ h g f → ≡ᵗ-≡ (∘ᵗ-assoc h g f)
          ; 𝟙ᵐ               = 𝟙ᵗ
          ; terminalᵐ        = terminalᵗ
          ; terminalᵐ-unique = ≡ᵗ-≡ terminalᵗ-unique
          ; 𝟘ᵐ               = 𝟘ᵗ
          ; initialᵐ         = initialᵗ
          ; initialᵐ-unique  = ≡ᵗ-≡ initialᵗ-unique
          ; _×ᵐ_             = _×ᵗ_
          ; fstᵐ             = fstᵗ
          ; sndᵐ             = sndᵗ
          ; ⟨_,_⟩ᵐ           = ⟨_,_⟩ᵗ
          ; ⟨⟩ᵐ-fstᵐ         = λ f g → ≡ᵗ-≡ (⟨⟩ᵗ-fstᵗ f g)
          ; ⟨⟩ᵐ-sndᵐ         = λ f g → ≡ᵗ-≡ (⟨⟩ᵗ-sndᵗ f g)
          ; ⟨⟩ᵐ-unique       = λ f g h p q → ≡ᵗ-≡ (⟨⟩ᵗ-unique f g h (≡-≡ᵗ p) (≡-≡ᵗ q))
          ; Π                = Πᵗ
          ; projᵐ            = projᵗ
          ; ⟨_⟩ᵢᵐ            = ⟨_⟩ᵢᵗ
          ; mapⁱˣᵐ-identity  = λ {I} {A} → ≡ᵗ-≡ (mapⁱˣᵗ-identity {I} {A})
          ; mapⁱˣᵐ-∘ᵐ        = λ f g → ≡ᵗ-≡ (mapⁱˣᵗ-∘ᵗ f g)
          ; ⟨⟩ᵢᵐ-projᵐ       = λ f i → ≡ᵗ-≡ (⟨⟩ᵢᵗ-projᵗ f i)
          ; ⟨⟩ᵢᵐ-∘ᵐ          = λ f g → ≡ᵗ-≡ (⟨⟩ᵢᵗ-∘ᵗ f g)
          ; _⇒ᵐ_             = _⇒ᵗ_
          ; appᵐ             = appᵗ
          ; map⇒ᵐ            = map⇒ᵗ
          ; curryᵐ           = curryᵗ
          ; uncurryᵐ         = uncurryᵗ
          ; map⇒ᵐ-identity   = ≡ᵗ-≡ map⇒ᵗ-identity
          ; curryᵐ-mapˣᵐ     = λ f g h → ≡ᵗ-≡ (curryᵗ-mapˣᵗ f g h)
          ; uncurryᵐ-mapˣᵐʳ  = λ f g → ≡ᵗ-≡ (uncurryᵗ-mapˣᵗʳ f g)
          } ;
  Fut = record
          { [_]ᵒ          = [_]ᵒ
          ; [_]ᶠ          = [_]ᶠ
          ; []-≤          = λ {A} → []-≤ {A}
          ; ε             = ε
          ; ε⁻¹           = ε⁻¹
          ; δ             = λ {A} → δ {A}
          ; δ⁻¹           = λ {A} → δ⁻¹ {A}
          ; []-idᵐ        = λ {A} → ≡ᵗ-≡ ([]-idᵗ {A})
          ; []-∘ᵐ         = λ f g → ≡ᵗ-≡ ([]-∘ᵗ f g)
          ; []-≤-nat      = λ f p → ≡ᵗ-≡ ([]-≤-nat f p)
          ; []-≤-refl     = λ {A} → ≡ᵗ-≡ ([]-≤-refl {A})
          ; []-≤-trans    = λ {A} p q → ≡ᵗ-≡ ([]-≤-trans {A} p q)
          ; []-ε-nat      = λ f → ≡ᵗ-≡ ([]-ε-nat f)
          ; []-ε⁻¹-nat    = λ f → ≡ᵗ-≡ ([]-ε⁻¹-nat f)
          ; []-δ-nat      = λ f → ≡ᵗ-≡ ([]-δ-nat f)
          ; []-δ⁻¹-nat    = λ f → ≡ᵗ-≡ ([]-δ⁻¹-nat f)
          ; []-δ-≤        = λ {A} p q → ≡ᵗ-≡ ([]-δ-≤ {A} p q)
          ; []-ε∘ε⁻¹≡id   = λ {A} → ≡ᵗ-≡ ([]-ε∘ε⁻¹≡id {A})
          ; []-ε⁻¹∘ε≡id   = λ {A} → ≡ᵗ-≡ ([]-ε⁻¹∘ε≡id {A})
          ; []-δ∘δ⁻¹≡id   = λ {A} → ≡ᵗ-≡ ([]-δ∘δ⁻¹≡id {A})
          ; []-δ⁻¹∘δ≡id   = λ {A} → ≡ᵗ-≡ ([]-δ⁻¹∘δ≡id {A})
          ; []-ε∘δ≡id     = λ {A} → ≡ᵗ-≡ ([]-ε∘δ≡id {A})
          ; []-Dε∘δ≡≤     = λ {A} → ≡ᵗ-≡ ([]-Dε∘δ≡≤ {A})
          ; []-δ∘δ≡Dδ∘δ∘≤ = λ {A} → ≡ᵗ-≡ ([]-δ∘δ≡Dδ∘δ∘≤ {A})
          ; []-monoidal   = λ {A} {B} → []-monoidal {A} {B}
          } ;
  Pas = record
          { ⟨_⟩ᵒ           = ⟨_⟩ᵒ
          ; ⟨_⟩ᶠ           = ⟨_⟩ᶠ
          ; ⟨⟩-≤           = λ {A} → ⟨⟩-≤ {A}
          ; η              = η
          ; η⁻¹            = η⁻¹
          ; μ              = λ {A} → μ {A}
          ; μ⁻¹            = λ {A} → μ⁻¹ {A}
          ; ⟨⟩-idᵐ         = λ {A} → ≡ᵗ-≡ (⟨⟩-idᵗ {A})
          ; ⟨⟩-∘ᵐ          = λ f g → ≡ᵗ-≡ (⟨⟩-∘ᵗ f g)
          ; ⟨⟩-≤-nat       = λ f p → ≡ᵗ-≡ (⟨⟩-≤-nat f p)
          ; ⟨⟩-≤-refl      = λ {A} → ≡ᵗ-≡ (⟨⟩-≤-refl {A})
          ; ⟨⟩-≤-trans     = λ {A} p q → ≡ᵗ-≡ (⟨⟩-≤-trans {A} p q)
          ; ⟨⟩-η-nat       = λ f → ≡ᵗ-≡ (⟨⟩-η-nat f)
          ; ⟨⟩-η⁻¹-nat     = λ f → ≡ᵗ-≡ (⟨⟩-η⁻¹-nat f)
          ; ⟨⟩-μ-nat       = λ f → ≡ᵗ-≡ (⟨⟩-μ-nat f)
          ; ⟨⟩-μ⁻¹-nat     = λ f → ≡ᵗ-≡ (⟨⟩-μ⁻¹-nat f)
          ; ⟨⟩-μ-≤         = λ {A} p q → ≡ᵗ-≡ (⟨⟩-μ-≤ {A} p q)
          ; ⟨⟩-μ-≤₁        = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ-≤₁ {A} p)
          ; ⟨⟩-μ-≤₂        = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ-≤₂ {A} p)
          ; ⟨⟩-μ⁻¹-≤₂      = λ {A} p → ≡ᵗ-≡ (⟨⟩-μ⁻¹-≤₂ {A} p)
          ; ⟨⟩-η∘η⁻¹≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-η∘η⁻¹≡id {A})
          ; ⟨⟩-η⁻¹∘η≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-η⁻¹∘η≡id {A})
          ; ⟨⟩-μ∘μ⁻¹≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘μ⁻¹≡id {A})
          ; ⟨⟩-μ⁻¹∘μ≡id    = λ {A} → ≡ᵗ-≡ (⟨⟩-μ⁻¹∘μ≡id {A})
          ; ⟨⟩-μ∘η≡id      = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘η≡id {A})
          ; ⟨⟩-μ∘Tη≡id     = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘Tη≡id {A})
          ; ⟨⟩-μ∘μ≡≤∘μ∘Tμ  = λ {A} → ≡ᵗ-≡ (⟨⟩-μ∘μ≡≤∘μ∘Tμ {A})
          ; ⟨⟩-Tη⁻¹∘μ⁻¹≡id = λ {A} → ≡ᵗ-≡ (⟨⟩-Tη⁻¹∘μ⁻¹≡id {A})
          } ;
  Adj = record
          { η⊣       = η⊣
          ; ε⊣       = ε⊣
          ; η⊣-nat   = λ f → ≡ᵗ-≡ (η⊣-nat f)
          ; ε⊣-nat   = λ f → ≡ᵗ-≡ (ε⊣-nat f)
          ; ε⊣∘Fη≡id = λ {A} → ≡ᵗ-≡ (ε⊣∘Fη≡id {A})
          ; Gε⊣∘η≡id = λ {A} → ≡ᵗ-≡ (Gε⊣∘η≡id {A})
          ; η⊣≡ε⁻¹∘η = λ {A} → ≡ᵗ-≡ (η⊣≡ε⁻¹∘η {A})
          ; ε⊣≡ε∘η⁻¹ = λ {A} → ≡ᵗ-≡ (ε⊣≡ε∘η⁻¹ {A})
          } ;
  Typ = record
          { ConstObj = λ B → ConstTSet (BaseSet B)
          ; constᵐ   = λ c → constᵗ c
          } ;
  Mon = record
          { Tᵒ                       = {!!}
          ; Tᶠ                       = {!!}
          ; ηᵀ                       = {!!}
          ; μᵀ                       = {!!}
          ; τ-substᵀ                 = {!!}
          ; Tᶠ-idᵐ                   = {!!}
          ; Tᶠ-∘ᵐ                    = {!!}
          ; ηᵀ-nat                   = {!!}
          ; μᵀ-nat                   = {!!}
          ; μᵀ-identity₁             = {!!}
          ; μᵀ-identity₂             = {!!}
          ; μᵀ-assoc                 = {!!}
          ; delayᵀ                   = {!!}
          ; opᵀ                      = {!!}
          ; delayᵀ-nat               = {!!}
          ; opᵀ-nat                  = {!!}
          ; delayᵀ-algebraicity      = {!!}
          ; opᵀ-algebraicity         = {!!}
          ; strᵀ                     = {!!}
          ; strᵀ-nat                 = {!!}
          ; strᵀ-delayᵀ-algebraicity = {!!}
          ; T-alg-of-handlerᵀ        = {!!}
          }
  }
