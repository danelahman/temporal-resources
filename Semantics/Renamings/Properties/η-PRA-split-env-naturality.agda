----------------------------------------------------------
-- Naturality of the PRA unit wrt environment splitting --
----------------------------------------------------------

open import Semantics.Model

module Semantics.Renamings.Properties.η-PRA-split-env-naturality (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod
open import Semantics.Interpretation.Properties.split-env-isomorphism Mod
open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.eq-ren Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

η-PRA-split-env-nat : ∀ {Γ Γ' A}
                       → (τ : Time)
                       → (p : τ ≤ ctx-time Γ')
                       →    η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p 
                         ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
                       ≡    ⟨ τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
                         ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
                         ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
                              (≤-trans p
                                (≤-trans
                                  (m≤n+m (ctx-time Γ') (ctx-time Γ))
                                  (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))

η-PRA-split-env-nat {Γ} {[]} {A} zero p =
  begin
       η
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityʳ _ ⟩
       η
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ∎
η-PRA-split-env-nat {Γ} {Γ' ∷ B} {A} zero p =
  begin
       η
    ∘ᵐ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩-η-nat _) ⟩
       ⟨ 0 ⟩ᶠ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟨ 0 ⟩ᶠ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-idᵐ)) ⟩
       ⟨ 0 ⟩ᶠ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ∎
η-PRA-split-env-nat {Γ} {Γ' ∷ B} {A} (suc τ) p =
  begin
       (   η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} (suc τ) p
        ∘ᵐ fstᵐ)
    ∘ᵐ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} (suc τ) p
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
       η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} (suc τ) p
    ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
    ∘ᵐ fstᵐ 
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} (suc τ) p
        ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl))
    ∘ᵐ fstᵐ 
  ≡⟨ ∘ᵐ-congˡ (η-PRA-split-env-nat {Γ} {Γ'} {A} (suc τ) p) ⟩
       (   ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ suc τ} (≡-split refl))
        ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ} p) ⟧ʳ
        ∘ᵐ η-PRA {Γ ++ᶜ Γ'} (suc τ)
             (≤-trans p
               (≤-trans
                 (m≤n+m (ctx-time Γ') (ctx-time Γ))
                 (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
    ∘ᵐ fstᵐ 
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ suc τ} (≡-split refl))
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} (suc τ)
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ fstᵐ 
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
      (cong (η-PRA {Γ ++ᶜ Γ'} (suc τ)) (≤-irrelevant _ _)))) ⟩
       ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ suc τ} (≡-split refl))
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} {A} (suc τ)
         (≤-trans p
          (≤-trans
           (subst (_≤_ (ctx-time Γ')) (+-comm (ctx-time Γ') (ctx-time Γ))
            (m≤m+n (ctx-time Γ') (ctx-time Γ)))
           (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ fstᵐ
  ∎
η-PRA-split-env-nat {Γ} {Γ' ⟨ τ' ⟩} {A} zero p =
  begin
       η
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ sym (⟨⟩-η-nat _) ⟩
       ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ idᵐ
    ∘ᵐ η
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-idᵐ)) ⟩
       ⟨ 0 ⟩ᶠ (⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ ⟨ 0 ⟩ᶠ idᵐ
    ∘ᵐ η
  ∎
η-PRA-split-env-nat {Γ} {Γ' ⟨ τ' ⟩} {A} (suc τ) p with suc τ ≤? τ'
... | yes q =
  begin
       (   μ⁻¹
        ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-≤-nat _ _)) ⟩
       μ⁻¹
    ∘ᵐ ⟨ (suc τ) + (τ' ∸ suc τ) ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
       (   μ⁻¹
        ∘ᵐ ⟨ (suc τ) + (τ' ∸ suc τ) ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩-μ⁻¹-nat _)) ⟩
       (   ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
        ∘ᵐ μ⁻¹)
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ idᵐ
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-idᵐ)) ⟩
       ⟨ suc τ ⟩ᶠ (⟨ τ' ∸ suc τ ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl)))
    ∘ᵐ ⟨ suc τ ⟩ᶠ idᵐ
    ∘ᵐ μ⁻¹
    ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
  ∎
... | no ¬q =
  begin
       (   ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
        ∘ᵐ μ
        ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA (suc τ ∸ τ')
                     (≤-trans (∸-monoˡ-≤ τ' p)
                      (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA (suc τ ∸ τ')
                 (≤-trans (∸-monoˡ-≤ τ' p)
                  (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ'))))
    ∘ᵐ ⟨ τ' ⟩ᶠ (split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩-∘ᵐ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   η-PRA (suc τ ∸ τ')
                    (≤-trans (∸-monoˡ-≤ τ' p)
                     (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                ∘ᵐ split-env {Γ ++ᶜ Γ'} {Γ} (≡-split refl))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (η-PRA-split-env-nat (suc τ ∸ τ')
        (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨ suc τ ∸ τ' ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
                ∘ᵐ ⟨ suc τ ∸ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ ∸ τ'}
                                       (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ
                ∘ᵐ η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                     (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                       (≤-trans
                         (m≤n+m (ctx-time Γ') (ctx-time Γ))
                         (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ (sym (∘ᵐ-assoc _ _ _)))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   (   ⟨ suc τ ∸ τ' ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
                    ∘ᵐ ⟨ suc τ ∸ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ ∸ τ'}
                                          (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ)
                ∘ᵐ η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                     (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                       (≤-trans
                         (m≤n+m (ctx-time Γ') (ctx-time Γ))
                         (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (   ⟨ suc τ ∸ τ' ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
                ∘ᵐ ⟨ suc τ ∸ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ ∸ τ'}
                                       (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl)))
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ ∸ τ'}
                                       (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-μ-nat _))) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (⟨ suc τ ∸ τ' ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {suc τ ∸ τ'}
                                       (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ)
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-μ-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
       ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
    ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _))) (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ ⟨ τ' + (suc τ ∸ τ') ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-≤-nat _ _))) (∘ᵐ-assoc _ _ _))) ⟩
       ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')
                  (≤-trans (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))
                    (≤-trans
                      (m≤n+m (ctx-time Γ') (ctx-time Γ))
                      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ τ' ⟩ᶠ
      (cong (η-PRA {Γ ++ᶜ Γ'} (suc τ ∸ τ')) (≤-irrelevant _ _)))))) ⟩
       ⟨ suc τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ (suc τ ∸ τ')} (≡-split refl))
    ∘ᵐ ⟨ suc τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ (≤-trans (∸-monoˡ-≤ τ' p) (≤-reflexive (m+n∸n≡m (ctx-time Γ') τ')))) ⟧ʳ
    ∘ᵐ ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
    ∘ᵐ μ
    ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA (suc τ ∸ τ')
                 (≤-trans
                  (∸-monoˡ-≤ τ'
                   (≤-trans p
                    (≤-trans
                     (subst (_≤_ (ctx-time Γ' + τ'))
                      (+-comm (ctx-time Γ' + τ') (ctx-time Γ))
                      (m≤m+n (ctx-time Γ' + τ') (ctx-time Γ)))
                     (≤-reflexive
                      (sym
                       (trans (cong (_+ τ') (ctx-time-++ᶜ Γ Γ'))
                        (+-assoc (ctx-time Γ) (ctx-time Γ') τ')))))))
                  (≤-reflexive (m+n∸n≡m (ctx-time (Γ ++ᶜ Γ')) τ'))))
  ∎



η-PRA-split-env⁻¹-nat : ∀ {Γ Γ' A}
                         → (τ : Time)
                         → (p : τ ≤ ctx-time Γ')
                         →    η-PRA {Γ ++ᶜ Γ'} {A = A} τ
                                (≤-trans p
                                  (≤-trans
                                    (m≤n+m (ctx-time Γ') (ctx-time Γ))
                                    (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
                           ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
                         ≡    ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
                           ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
                           ∘ᵐ η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p

η-PRA-split-env⁻¹-nat {Γ} {Γ'} {A} τ p =
  begin
       η-PRA {Γ ++ᶜ Γ'} {A = A} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congˡ (sym ⟨⟩-idᵐ) ⟩
       ⟨ τ ⟩ᶠ idᵐ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨⟩
       ⟨ τ ⟩ᶠ (⟦ eq-ren (refl {x = Γ ++ᶜ Γ' -ᶜ τ}) ⟧ʳ)
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ τ ⟩ᶠ
      (cong
        (λ q → ⟦ eq-ren {Γ ++ᶜ Γ' -ᶜ τ} {Γ ++ᶜ Γ' -ᶜ τ} q ⟧ʳ)
        {x = refl {x = Γ ++ᶜ Γ' -ᶜ τ}}
        {y = trans (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)}
        uip)) ⟩
       ⟨ τ ⟩ᶠ (⟦ eq-ren (trans (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ)
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congˡ (cong ⟨ τ ⟩ᶠ (sym
      (eq-ren-trans (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)))) ⟩
       ⟨ τ ⟩ᶠ (   ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
               ∘ᵐ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ)
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _)))) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym ⟨⟩-idᵐ)) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ idᵐ
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (⟨⟩-∘ᵐ _ _)))
      (∘ᵐ-congˡ (cong ⟨ τ ⟩ᶠ (split-env-split-env⁻¹-iso
                               {Γ ++ᶜ (Γ' -ᶜ τ)} {Γ} {Γ' -ᶜ τ} {A} (≡-split refl))))))) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
    ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
         (≤-trans p
           (≤-trans
             (m≤n+m (ctx-time Γ') (ctx-time Γ))
             (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ')))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ (   ⟨ τ ⟩ᶠ (split-env {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
        ∘ᵐ ⟨ τ ⟩ᶠ ⟦ eq-ren (++ᶜ-ᶜ {Γ} {Γ'} {τ} p) ⟧ʳ
        ∘ᵐ η-PRA {Γ ++ᶜ Γ'} τ
             (≤-trans p
               (≤-trans
                 (m≤n+m (ctx-time Γ') (ctx-time Γ))
                 (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (sym (η-PRA-split-env-nat τ p)))) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ (   η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p
        ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl))
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p
    ∘ᵐ split-env {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
    ∘ᵐ split-env⁻¹ {Γ' = Γ} {Γ'' = Γ'} (≡-split refl)
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (split-env⁻¹-split-env-iso {Γ ++ᶜ Γ'} {Γ} {Γ'} {A} (≡-split refl)))) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) ⟩
       ⟨ τ ⟩ᶠ ⟦ eq-ren (sym (++ᶜ-ᶜ {Γ} {Γ'} {τ} p)) ⟧ʳ
    ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ {Γ' = Γ} {Γ'' = Γ' -ᶜ τ} (≡-split refl))
    ∘ᵐ η-PRA {Γ'} {⟦ Γ ⟧ᵉᵒ A} τ p
  ∎
