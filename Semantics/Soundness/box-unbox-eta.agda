-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.box-unbox-eta (Mod : Model) where

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod
open import Semantics.Renamings.Properties.-ᶜ-wk-ren-decompose Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

box-unbox-eta-sound : ∀ {Γ A C}
                    → (V : Γ ⊢V⦂ [ 0 ] A)
                    → (M : Γ ∷ [ 0 ] A ⊢C⦂ C)
                    → ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ
                    ≡ ⟦ unbox z≤n V
                         (C-rename (exch-ren ∘ʳ wk-ren) M
                           [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c) ⟧ᶜᵗ

box-unbox-eta-sound {Γ} {A} {C} V M = 
  begin
    ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ
  ≡⟨ C-subst≡∘ᵐ M Hd V ⟩
      ⟦ M ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityˡ _) ⟩
      ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
      ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (
      begin
        ⟦ V ⟧ᵛᵗ
      ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _))
        (trans (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id) (∘ᵐ-identityˡ _))) ⟩
           η⁻¹
        ∘ᵐ η
        ∘ᵐ ⟦ V ⟧ᵛᵗ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩-η-nat _)) ⟩
           η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ sym (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ []-ε⁻¹∘ε≡id) (∘ᵐ-identityˡ _))) ⟩
           ε⁻¹
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ ⟨⟩-η⁻¹∘η≡id) (∘ᵐ-identityˡ _)))) ⟩
           ε⁻¹
        ∘ᵐ η⁻¹
        ∘ᵐ η
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym ([]-ε⁻¹-nat _))) (∘ᵐ-assoc _ _ _)) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ ε⁻¹
        ∘ᵐ η
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ idᵐ
        ∘ᵐ ε⁻¹
        ∘ᵐ η
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong [ 0 ]ᶠ (sym
          (trans (cong ⟨⟩-≤ (≤-irrelevant _ _)) ⟨⟩-≤-refl)))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ ε⁻¹
        ∘ᵐ η
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ η⊣≡ε⁻¹∘η) (∘ᵐ-assoc _ _ _)))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ η⊣
        ∘ᵐ ε
        ∘ᵐ η⁻¹
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans (∘ᵐ-congˡ ε⊣≡ε∘η⁻¹) (∘ᵐ-assoc _ _ _))))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ η⊣
        ∘ᵐ ε⊣
        ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ
        ∘ᵐ η
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ η⊣
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ idᵐ ,
             ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _))
          (trans (∘ᵐ-congˡ (sym (η⊣-nat _))) (∘ᵐ-assoc _ _ _)))) ⟩
           [ 0 ]ᶠ η⁻¹
        ∘ᵐ [ 0 ]ᶠ (⟨⟩-≤ z≤n)
        ∘ᵐ [ 0 ]ᶠ (⟨ 0 ⟩ᶠ sndᵐ)
        ∘ᵐ η⊣
        ∘ᵐ ⟨ idᵐ ,
             ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
      ≡⟨ sym (trans (∘ᵐ-congˡ (trans ([]-∘ᵐ _ _) (∘ᵐ-congˡ ([]-∘ᵐ _ _))))
          (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _))) ⟩
           [ 0 ]ᶠ (   (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
                   ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ)
        ∘ᵐ η⊣
        ∘ᵐ ⟨ idᵐ ,
             ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   [ 0 ]ᶠ (   (η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n)
                       ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ)
            ∘ᵐ η⊣)
        ∘ᵐ ⟨ idᵐ ,
             ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
      ∎)) ⟩
      ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
         ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (sym
      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-identityˡ _)
        (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (trans (∘ᵐ-assoc _ _ _)
          (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-identityˡ _))))))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
            (idᵐ ∘ᵐ sndᵐ)
         ∘ᵐ ⟨    idᵐ
              ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                      ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                   ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
            ,
               (   sndᵐ
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ ,
                     idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                    ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ 
  ≡⟨ ∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ (sym (trans (∘ᵐ-assoc _ _ _)
      (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
          (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (trans (∘ᵐ-assoc _ _ _)
            (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))))))))) refl) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨    (((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ)
         ∘ᵐ ⟨    idᵐ
              ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                      ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                   ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
            ,
               (   sndᵐ
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ ,
                       idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                    ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ ⟩ᵐ
       ,
            (idᵐ ∘ᵐ sndᵐ)
         ∘ᵐ ⟨    idᵐ
              ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                      ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                   ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
            ,
               (   sndᵐ
                ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ ,
                     idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                    ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
                 ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ 
  ≡⟨ ∘ᵐ-congʳ (trans (⟨⟩ᵐ-∘ᵐ _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
            ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
         ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
            ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
         ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ idᵐ
         ∘ᵐ ⟨ idᵐ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ,
                 ([ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣)
              ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ ⟩ᵐ ,
         _ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (⟨⟩ᵐ-∘ᵐ _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _)))))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ (⟨    ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
          ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-assoc _ _ _)))) ⟩
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ fstᵐ
    ∘ᵐ ⟨   (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
        ∘ᵐ fstᵐ ,
           idᵐ
        ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       (   (   ⟦ M ⟧ᶜᵗ
            ∘ᵐ fstᵐ
            ∘ᵐ ⟨   (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ ,
                   idᵐ
                ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
        ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       (   (   ⟦ M ⟧ᶜᵗ
            ∘ᵐ fstᵐ
            ∘ᵐ ⟨   (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ ,
                   idᵐ
                ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
        ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
        ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
       (   (   ⟦ M ⟧ᶜᵗ
            ∘ᵐ fstᵐ
            ∘ᵐ ⟨   (   ⟨ ((idᵐ ∘ᵐ fstᵐ) ∘ᵐ fstᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                    ∘ᵐ ⟨ idᵐ , sndᵐ ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
                ∘ᵐ fstᵐ ,
                   idᵐ
                ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ ⟨ idᵐ , (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟨ ⟦ Γ ⟧ᵉᶠ terminalᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ)
        ∘ᵐ idᵐ
        ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
        ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (∘ᵐ-congˡ (sym (C-rename≡∘ᵐ _ M))) ⟩
       (⟦ C-rename
           ((var-ren (Tl-∷ Hd) ∘ʳ
             cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
            ∘ʳ wk-ren) M ⟧ᶜᵗ
       ∘ᵐ idᵐ
       ∘ᵐ ⟨ idᵐ , [ 0 ]ᶠ ((η⁻¹ ∘ᵐ ⟨⟩-≤ z≤n) ∘ᵐ ⟨ 0 ⟩ᶠ sndᵐ) ∘ᵐ η⊣ ⟩ᵐ
       ∘ᵐ idᵐ)
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ≡⟨ ∘ᵐ-congˡ (sym
      (C-subst≡∘ᵐ (C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
                       cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
                      ∘ʳ wk-ren) M) Hd (box (var (Tl-⟨⟩ Hd))))) ⟩
                  ⟦ C-rename ((var-ren (Tl-∷ Hd) ∘ʳ
           cong-∷-ren (var-ren Hd ∘ʳ cong-∷-ren (wk-ren ∘ʳ wk-ren ∘ʳ id-ren)))
          ∘ʳ wk-ren) M [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨ 0 ⟩ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η ⟩ᵐ
  ∎

