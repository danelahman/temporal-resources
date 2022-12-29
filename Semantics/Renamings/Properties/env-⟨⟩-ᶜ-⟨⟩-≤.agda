-------------------------------------------------------------------------------
-- The minus operation on environments interaction with monotonicity in time --
-------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-⟨⟩-≤ (Mod : Model) where

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

postulate
  env-⟨⟩-ᶜ-⟨⟩-≤ : ∀ {Γ τ τ' A}
                → (p : τ' ≤ ctx-time Γ)
                → (q : τ ≤ τ')
                →    ⟨⟩-≤ q
                  ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} τ' p 
                ≡    ⟨ τ ⟩ᶠ ⟦ -ᶜ-≤-ren {Γ} q ⟧ʳ
                  ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} τ (≤-trans q p)

