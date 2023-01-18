-------------------------------------------------------
-- Naturality of the minus operation on environments --
-------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.η-PRA-eq-ren-naturality (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

η-PRA-eq-ren-nat : ∀ {Γ Γ' A}
                    → (τ : Time)
                    → (p : τ ≤ ctx-time Γ')
                    → (q : Γ' ≡ Γ)
                    →    η-PRA {Γ'} {A} τ p 
                      ∘ᵐ ⟦ eq-ren q ⟧ʳ
                    ≡    ⟨ τ ⟩ᶠ ⟦ eq-ren (cong (_-ᶜ τ) q) ⟧ʳ
                      ∘ᵐ η-PRA τ (≤-trans p (≤-reflexive (cong ctx-time q)))

η-PRA-eq-ren-nat τ p refl = 
  begin
       η-PRA τ p
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
    η-PRA τ p
  ≡⟨ cong (η-PRA τ) (≤-irrelevant _ _) ⟩
    η-PRA τ (≤-trans p (≤-reflexive refl))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ η-PRA τ (≤-trans p (≤-reflexive refl))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ τ ⟩ᶠ idᵐ
    ∘ᵐ η-PRA τ (≤-trans p (≤-reflexive refl))
  ∎
