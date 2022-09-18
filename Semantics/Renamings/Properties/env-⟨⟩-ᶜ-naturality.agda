----------------------------------------------------------------------------------
-- Relating the syntactic actions of renamings to semantic morphism composition --
----------------------------------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.env-⟨⟩-ᶜ-naturality (Mod : Model) where


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

-- TODO: finish typing up the proof later

env-⟨⟩-ᶜ-nat : ∀ {Γ Γ'}
             → (τ : Time)
             → (p : τ ≤ ctx-time Γ)
             → (ρ : Ren Γ Γ')
             →    env-⟨⟩-ᶜ {Γ} τ p
               ∘ᵐ ⟦ ρ ⟧ʳ
            ≡    ⟨ τ ⟩ᶠ ⟦ ρ -ʳ τ ⟧ʳ
               ∘ᵐ env-⟨⟩-ᶜ τ (≤-trans p (ren-≤-ctx-time ρ))

env-⟨⟩-ᶜ-nat zero p ρ = 
  begin
    η ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ sym (⟨⟩-η-nat _) ⟩
    ⟨ zero ⟩ᶠ ⟦ ρ ⟧ʳ ∘ᵐ η
  ∎
env-⟨⟩-ᶜ-nat {Γ ∷ A} {Γ'} (suc τ) p ρ =
  begin
    (env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵐ fstᵐ) ∘ᵐ ⟦ ρ ⟧ʳ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵐ (fstᵐ ∘ᵐ ⟦ ρ ⟧ʳ)
  ≡⟨⟩
    env-⟨⟩-ᶜ {Γ} (suc τ) p ∘ᵐ ⟦ ρ ∘ʳ wk-ren ⟧ʳ
  ≡⟨ env-⟨⟩-ᶜ-nat (suc τ) p (ρ ∘ʳ wk-ren) ⟩
       ⟨ suc τ ⟩ᶠ (idᵐ ∘ᵐ ⟦ ρ -ʳ suc τ ⟧ʳ)
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans ≤-refl (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ suc τ ⟩ᶠ (∘ᵐ-identityˡ _)) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (≤-trans ≤-refl (ren-≤-ctx-time ρ)))
  ≡⟨ ∘ᵐ-congʳ (cong (λ p → env-⟨⟩-ᶜ {Γ'} (suc τ) p) (≤-irrelevant _ _)) ⟩
       ⟨ suc τ ⟩ᶠ ⟦ ρ -ʳ suc τ ⟧ʳ
    ∘ᵐ env-⟨⟩-ᶜ {Γ'} (suc τ) (≤-trans p (ren-≤-ctx-time ρ))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p id-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
       μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)) ⟩
       (   idᵐ
        ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ})
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       idᵐ
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
    ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q =
  begin
         (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
          ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
          ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                       (≤-trans (∸-monoˡ-≤ τ' p)
                        (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
      ∘ᵐ idᵐ
    ≡⟨ ∘ᵐ-identityʳ _ ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' p)
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _)))) ⟩
         ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
         idᵐ
      ∘ᵐ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
    ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
         ⟨ suc τ ⟩ᶠ idᵐ
      ∘ᵐ ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
      ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
      ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                   (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                    (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (ρ ∘ʳ ρ') = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p wk-ren with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ (   μ⁻¹ {⟦ Γ ⟧ᵉ}
        ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ fstᵐ
  ∎
... | no ¬q =
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p)
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (cong (env-⟨⟩-ᶜ (suc τ ∸ τ')) (≤-irrelevant _ _))))) ⟩
       (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ (   ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ}
        ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' (≤-trans p (≤-reflexive refl)))
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ')))))
    ∘ᵐ fstᵐ
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ .0 ⟩} (suc τ) p ⟨⟩-η-ren = 
  begin
       (   ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
        ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
        ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                    (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))))
    ∘ᵐ η {⟦ Γ ⟧ᵉ}
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵐ ⟨ 0 ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ)
                (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0))))
    ∘ᵐ η {⟦ Γ ⟧ᵉ}
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-η-nat _)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵐ μ {⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵐ η {⟨ suc τ  ⟩ᵒ ⟦ Γ -ᶜ suc τ ⟧ᵉ}
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ⟨⟩-μ∘η≡id)) ⟩
       ⟨⟩-≤ {⟦ Γ -ᶜ suc τ ⟧ᵉ} ≤-refl
    ∘ᵐ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congˡ ⟨⟩-≤-refl ⟩
       idᵐ
    ∘ᵐ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans (∸-monoˡ-≤ 0 p) (≤-reflexive (m+n∸n≡m (ctx-time Γ) 0)))
  ≡⟨ ∘ᵐ-congʳ (cong (env-⟨⟩-ᶜ {Γ} (suc τ)) (≤-irrelevant _ _)) ⟩
       idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ env-⟨⟩-ᶜ {Γ} (suc τ)
         (≤-trans p (≤-reflexive (+-identityʳ (ctx-time Γ))))
  ∎
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p ⟨⟩-η⁻¹-ren with suc τ ≤? τ'
... | yes q = 
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ η⁻¹
  ≡⟨ ∘ᵐ-congʳ (⟨⟩-η⁻¹-nat _) ⟩
       μ⁻¹
    ∘ᵐ η⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ η⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (⟨⟩-η⁻¹-nat _) ⟩
       (   η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (
      begin
        η⁻¹
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
           idᵐ
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-μ∘η≡id) ⟩
           (   μ
            ∘ᵐ η)
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           μ
        ∘ᵐ η
        ∘ᵐ η⁻¹
      ≡⟨ ∘ᵐ-congʳ ⟨⟩-η∘η⁻¹≡id ⟩
           μ
        ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        μ
      ∎)) ⟩
       (   μ
        ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹)
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-≤-refl) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ μ⁻¹
    ∘ᵐ ⟨ 0 ⟩ᶠ (⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨⟩-≤ ≤-refl
    ∘ᵐ μ
    ∘ᵐ ⟨ 0 ⟩ᶠ (μ⁻¹ ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
  ∎
... | no ¬q = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ .(τ' + τ'') ⟩} (suc τ) p (⟨⟩-μ-ren {τ = τ'} {τ' = τ''}) = {!!}
env-⟨⟩-ᶜ-nat {.(_ ⟨ _ ⟩) ⟨ τ' ⟩} (suc τ) p ⟨⟩-μ⁻¹-ren = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (⟨⟩-≤-ren x) = {!!}
env-⟨⟩-ᶜ-nat {Γ ⟨ τ' ⟩} (suc τ) p (cong-⟨⟩-ren ρ) = {!!}

