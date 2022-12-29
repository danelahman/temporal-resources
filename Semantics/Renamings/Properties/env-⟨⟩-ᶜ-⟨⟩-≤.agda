{-# OPTIONS --allow-unsolved-metas #-}

-- Due to the eta-contraction bug leading to Agda generating
-- ill-typed `with` terms there are some unfilled holes below.

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
open import Semantics.Renamings.Properties.split-env-eq-ren Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

env-⟨⟩-ᶜ-⟨⟩-≤ : ∀ {Γ τ τ' A}
              → (p : τ' ≤ ctx-time Γ)
              → (q : τ ≤ τ')
              →    ⟨⟩-≤ q
                ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} τ' p 
              ≡    ⟨ τ ⟩ᶠ ⟦ -ᶜ-≤-ren {Γ} q ⟧ʳ
                ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} τ (≤-trans q p)

env-⟨⟩-ᶜ-⟨⟩-≤ {Γ} {zero} {zero} {A} p z≤n =
  begin
       ⟨⟩-≤ z≤n
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ ⟨⟩-≤-refl ⟩
        idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ 0 ⟩ᶠ (sym (trans (∘ᵐ-identityˡ _)
      (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))) ⟩
       ⟨ 0 ⟩ᶠ (idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ ∘ᵐ idᵐ)
    ∘ᵐ η
  ∎

env-⟨⟩-ᶜ-⟨⟩-≤ {Γ ∷ B} {zero} {suc τ'} {A} p q =
  begin
       ⟨⟩-≤ q
    ∘ᵐ env-⟨⟩-ᶜ {Γ ∷ B} {A} (suc τ') p
  ≡⟨⟩
       ⟨⟩-≤ q
    ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} (suc τ') p
    ∘ᵐ fstᵐ
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (env-⟨⟩-ᶜ-⟨⟩-≤ {Γ} p q)) (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ zero ⟩ᶠ ⟦ -ᶜ-≤-ren q ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} {A} zero (≤-trans q p)
    ∘ᵐ fstᵐ
  ≡⟨⟩
       ⟨ zero ⟩ᶠ ⟦ -ᶜ-≤-ren q ⟧ʳ
    ∘ᵐ η
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-η-nat _)) ⟩
       ⟨ zero ⟩ᶠ ⟦ -ᶜ-≤-ren {Γ} q ⟧ʳ
    ∘ᵐ ⟨ zero ⟩ᶠ fstᵐ
    ∘ᵐ η
  ≡⟨⟩
       ⟨ zero ⟩ᶠ ⟦ -ᶜ-≤-ren {Γ} q ⟧ʳ
    ∘ᵐ ⟨ zero ⟩ᶠ fstᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ ∷ B} {A} zero (≤-trans q p)
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨ zero ⟩ᶠ (   ⟦ -ᶜ-≤-ren {Γ} q ⟧ʳ
                  ∘ᵐ fstᵐ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ ∷ B} {A} zero (≤-trans q p)
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ zero ⟩ᶠ (
      begin
           (   ⟦ eq-ren (cong (_-ᶜ_ Γ) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
            ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ Γ) (+-∸-assoc zero q)) ⟧ʳ
            ∘ᵐ idᵐ
            ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ)
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) ⟩
           (   ⟦ eq-ren (cong (_-ᶜ_ Γ) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
            ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ Γ) (+-∸-assoc zero q)) ⟧ʳ
            ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ)
        ∘ᵐ fstᵐ
      ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
           ⟦ eq-ren (cong (_-ᶜ_ Γ) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
        ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ Γ) (+-∸-assoc zero q)) ⟧ʳ
        ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congˡ (cong (λ p → ⟦ eq-ren p ⟧ʳ)
                    {x = cong (_-ᶜ_ Γ) (sym (m+n∸m≡n zero (suc τ')))}
                    {y = cong (_-ᶜ_ (Γ ∷ B)) (sym (m+n∸m≡n zero (suc τ')))}
                    uip) ⟩
           ⟦ eq-ren (cong (_-ᶜ_ (Γ ∷ B)) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
        ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ Γ) (+-∸-assoc zero q)) ⟧ʳ
        ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong (λ p → ⟦ eq-ren p ⟧ʳ)
                              {x = cong (_-ᶜ_ Γ) (+-∸-assoc zero q)}
                              {y = cong (_-ᶜ_ (Γ ∷ B)) (+-∸-assoc zero q)}
                              uip)) ⟩
           ⟦ eq-ren (cong (_-ᶜ_ (Γ ∷ B)) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
        ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ (Γ ∷ B)) (+-∸-assoc zero q)) ⟧ʳ
        ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
           ⟦ eq-ren (cong (_-ᶜ_ (Γ ∷ B)) (sym (m+n∸m≡n zero (suc τ')))) ⟧ʳ
        ∘ᵐ ⟦ eq-ren (cong (_-ᶜ_ (Γ ∷ B)) (+-∸-assoc zero q)) ⟧ʳ
        ∘ᵐ idᵐ
        ∘ᵐ ⟦ -ᶜ-wk-ren {Γ} (suc τ') ⟧ʳ
        ∘ᵐ fstᵐ
      ∎)) ⟩
       ⟨ zero ⟩ᶠ ⟦ -ᶜ-≤-ren {Γ ∷ B} q ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ ∷ B} {A} zero (≤-trans q p)
  ∎

env-⟨⟩-ᶜ-⟨⟩-≤ {Γ ⟨ τ'' ⟩} {zero} {suc τ'} {A} p q = {!!}  -- doing `with suc τ' ≤? τ''` here generates an ill-typed Agda term

env-⟨⟩-ᶜ-⟨⟩-≤ {Γ} {suc τ} {suc τ'} {A} p q = {!!}  -- omitted for now, ill-typed `with`-generated terms hiding in here as well
