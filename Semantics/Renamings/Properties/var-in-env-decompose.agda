----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.var-in-env-decompose (Mod : Model) where

open import Data.Product

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Renamings.Core Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

var-in-env-decompose : ∀ {Γ A τ}
                     → (x : A ∈[ τ ] Γ)
                     → var-in-env x
                    ≡ᵐ    sndᵐ
                       ∘ᵐ ε-⟨⟩ {(⟦ proj₁ (var-split x) ⟧ᵉᵒ 𝟙ᵐ ×ᵐ ⟦ A ⟧ᵛ)}
                       ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
                       ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
var-in-env-decompose {Γ ∷ A} {.A} {.0} Hd = 
  begin
    sndᵐ
  ≡⟨ ≡ᵐ-sym (∘ᵐ-identityʳ _) ⟩
       sndᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (≡ᵐ-sym ⟨⟩-η⁻¹∘η≡id) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-identityˡ _))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ idᵐ
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≡ᵐ-sym ⟨⟩-≤-refl))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} ≤-refl
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≡-≡ᵐ (cong ⟨⟩-≤ (≤-irrelevant _ _))))) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨ ∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ η {⟦ Γ ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
  ≡⟨⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-identityʳ _))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ η
    ∘ᵐ idᵐ
  ∎
var-in-env-decompose {Γ ∷ B} {A} {τ} (Tl-∷ x) = 
  begin
       var-in-env x
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (var-in-env-decompose x) ⟩
       ((   sndᵐ
         ∘ᵐ ε-⟨⟩
         ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
         ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))))
    ∘ᵐ fstᵐ
  ≡⟨ ≡ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (≡ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
    ∘ᵐ fstᵐ
    ∘ᵐ mapˣᵐ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ (   env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
        ∘ᵐ fstᵐ)
    ∘ᵐ mapˣᵐ (split-env (proj₁ (proj₂ (proj₂ (var-split x))))) idᵐ
  ∎
var-in-env-decompose {Γ ⟨ τ ⟩} {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) = 
  begin
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)
  ≡⟨ ∘ᵐ-congʳ (≡-≡ᵐ (cong ⟨ τ ⟩ᶠ (≡ᵐ-≡ (var-in-env-decompose x)))) ⟩
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ (   sndᵐ
               ∘ᵐ ε-⟨⟩
               ∘ᵐ env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))
               ∘ᵐ split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ
      (≡ᵐ-trans
        (⟨⟩-∘ᵐ _ _)
        (∘ᵐ-congʳ (
          ≡ᵐ-trans
            (⟨⟩-∘ᵐ _ _)
            (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))) ⟩
       ε-⟨⟩
    ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ≡ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩
       (   (η⁻¹ ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ sndᵐ)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congˡ (
      ≡ᵐ-trans
        (∘ᵐ-congʳ (≡ᵐ-sym (⟨⟩-≤-nat _ _)))
        (≡ᵐ-trans
          (≡ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≡ᵐ-trans
            (∘ᵐ-congˡ (≡ᵐ-sym (⟨⟩-η⁻¹-nat _)))
            (∘ᵐ-assoc _ _ _)))) ⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (ε-⟨⟩ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (   η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
               ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (≡ᵐ-trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _)) ⟩
       (   sndᵐ
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ≡ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
    ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (
      begin
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-identityˡ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ idᵐ
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-trans (∘ᵐ-congˡ (≡ᵐ-sym ⟨⟩-μ⁻¹∘μ≡id)) (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨ τ ⟩ᶠ (η⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ})
        ∘ᵐ μ⁻¹ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ (≡ᵐ-trans (≡ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-Tη⁻¹∘ᵐμ⁻¹≡id)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (sym (+-identityʳ _)))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ≡ᵐ-trans (≡ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (⟨⟩-≤-trans _ _)) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ ((⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n))
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ∘ᵐ-congʳ
          (≡ᵐ-trans
            (≡ᵐ-sym (∘ᵐ-assoc _ _ _))
            (≡ᵐ-trans
              (∘ᵐ-congˡ (≡ᵐ-sym (⟨⟩-μ-≤₂ _)))
              (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (+-monoʳ-≤ τ z≤n)
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ≡⟨ ≡ᵐ-trans
          (≡ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≡ᵐ-trans
            (∘ᵐ-congˡ (⟨⟩-≤-trans _ _))
            (≡ᵐ-trans
              (∘ᵐ-congˡ (≡ᵐ-sym (⟨⟩-≤-trans _ _)))
              (∘ᵐ-assoc _ _ _))) ⟩
           ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
        ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
      ∎)) ⟩
       sndᵐ
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (≡ᵐ-sym (∘ᵐ-assoc _ _ _)) ⟩
       sndᵐ
    ∘ᵐ (   η⁻¹
        ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} z≤n)
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
    ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
    ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x))))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (≡ᵐ-sym (≡ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       sndᵐ
    ∘ᵐ ε-⟨⟩
    ∘ᵐ (   ⟨⟩-≤ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ} (≤-reflexive (+-comm (ctx-time (proj₁ (proj₂ (var-split x)))) τ))
        ∘ᵐ μ {⟦ proj₁ (var-split (Tl-⟨⟩ {τ = τ} x)) ⟧ᵉ ×ᵐ ⟦ A ⟧ᵛ}
        ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ (proj₁ (proj₂ (var-split x)))))
      ∘ᵐ ⟨ τ ⟩ᶠ (split-env (proj₁ (proj₂ (proj₂ (var-split x)))))
  ∎
