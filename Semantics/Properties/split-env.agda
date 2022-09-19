---------------------------------------------------
-- Properties of environment splitting morphisms --
---------------------------------------------------

open import Semantics.Model

module Semantics.Properties.split-env (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Renamings

open import Semantics.Interpretation Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

-- Environment splittings form an isomorphism

split-env-split-env⁻¹-iso : ∀ {Γ Γ' Γ'' A}
                          → (p : Γ' , Γ'' split Γ)
                          → split-env⁻¹ p ∘ᵐ split-env p
                          ≡ idᵐ {⟦ Γ ⟧ᵉᵒ A}

split-env-split-env⁻¹-iso split-[] = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
split-env-split-env⁻¹-iso (split-∷ p) = 
  begin
       ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨ (split-env⁻¹ p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
      (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (begin
         fstᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)) ⟩
         idᵐ ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congˡ (sym (split-env-split-env⁻¹-iso p)) ⟩
         (split-env⁻¹ p ∘ᵐ split-env p) ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         split-env⁻¹ p ∘ᵐ split-env p ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
         split-env⁻¹ p ∘ᵐ fstᵐ ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (split-env⁻¹ p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)
       (begin
         sndᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) ⟩
         idᵐ ∘ᵐ idᵐ ∘ᵐ sndᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
         idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)) ⟩
    idᵐ
  ∎
split-env-split-env⁻¹-iso (split-⟨⟩ {τ = τ} p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env⁻¹ p) ∘ᵐ ⟨ τ ⟩ᶠ (split-env p)
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (split-env⁻¹ p ∘ᵐ split-env p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env-split-env⁻¹-iso p) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎

split-env⁻¹-split-env-iso : ∀ {Γ Γ' Γ'' A}
                          → (p : Γ' , Γ'' split Γ)
                          → split-env p ∘ᵐ split-env⁻¹ p
                          ≡ idᵐ {⟦ Γ'' ⟧ᵉᵒ (⟦ Γ' ⟧ᵉᵒ A)}

split-env⁻¹-split-env-iso split-[] = 
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
split-env⁻¹-split-env-iso (split-∷ p) = 
  begin
       ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨ (split-env p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
      (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (begin
         fstᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)) ⟩
         idᵐ ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congˡ (sym (split-env⁻¹-split-env-iso p)) ⟩
         (split-env p ∘ᵐ split-env⁻¹ p) ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
         split-env p ∘ᵐ split-env⁻¹ p ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
         split-env p ∘ᵐ fstᵐ ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (split-env p ∘ᵐ fstᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)
       (begin
         sndᵐ ∘ᵐ idᵐ
       ≡⟨ trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))) ⟩
         idᵐ ∘ᵐ idᵐ ∘ᵐ sndᵐ
       ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
         idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env⁻¹ p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
       ∎)) ⟩
    idᵐ
  ∎
split-env⁻¹-split-env-iso (split-⟨⟩ {τ = τ} p) = 
  begin
    ⟨ τ ⟩ᶠ (split-env p) ∘ᵐ ⟨ τ ⟩ᶠ (split-env⁻¹ p)
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (split-env p ∘ᵐ split-env⁻¹ p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env⁻¹-split-env-iso p) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎


-- Environment splittings are natural

split-env-nat : ∀ {Γ Γ' Γ'' A B}
              → (p : Γ' , Γ'' split Γ)
              → (f : A →ᵐ B)
              →    ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
                ∘ᵐ split-env p
              ≡    split-env p
                ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
              
split-env-nat {Γ} {.Γ} {.[]} {A} {B} split-[] f = 
  begin
    ⟦ Γ ⟧ᵉᶠ f ∘ᵐ idᵐ
  ≡⟨ trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)) ⟩
    idᵐ ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
  ∎
split-env-nat {.(_ ∷ _)} {Γ'} {.(_ ∷ _)} {A} {B} (split-∷ {Γ' = Γ''} {Γ'' = Γ'''} p) f = 
  begin
       ⟨ ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
       ⟨    (⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f) ∘ᵐ fstᵐ)
         ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
            (idᵐ ∘ᵐ sndᵐ)
         ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (begin
           (⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f) ∘ᵐ fstᵐ)
        ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
        ∘ᵐ fstᵐ
        ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
           ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
        ∘ᵐ split-env p
        ∘ᵐ fstᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
            ∘ᵐ split-env p)
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congˡ (split-env-nat p f) ⟩
           (   split-env p
            ∘ᵐ ⟦ Γ''' ⟧ᵉᶠ f)
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           split-env p
        ∘ᵐ ⟦ Γ''' ⟧ᵉᶠ f
        ∘ᵐ fstᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-fstᵐ _ _)) ⟩
           split-env p
        ∘ᵐ fstᵐ
        ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (split-env p ∘ᵐ fstᵐ)
        ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎)
      (begin
        (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
        idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ⟩
        idᵐ ∘ᵐ idᵐ ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
        idᵐ ∘ᵐ sndᵐ ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
        (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎) ⟩
       ⟨ (split-env p ∘ᵐ fstᵐ) ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
         (idᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨ split-env p ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟦ Γ''' ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
split-env-nat {.(_ ⟨ _ ⟩)} {Γ'} {.(_ ⟨ _ ⟩)} {A} {B} (split-⟨⟩ {Γ' = Γ''} {Γ'' = Γ'''} {τ = τ} p) f =
  begin
    ⟨ τ ⟩ᶠ (⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)) ∘ᵐ ⟨ τ ⟩ᶠ (split-env p)
  ≡⟨ sym (⟨⟩-∘ᵐ _ _) ⟩
    ⟨ τ ⟩ᶠ (⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f) ∘ᵐ split-env p)
  ≡⟨ cong ⟨ τ ⟩ᶠ (split-env-nat p f) ⟩
    ⟨ τ ⟩ᶠ (split-env p ∘ᵐ ⟦ Γ''' ⟧ᵉᶠ f)
  ≡⟨ ⟨⟩-∘ᵐ _ _ ⟩
    ⟨ τ ⟩ᶠ (split-env p) ∘ᵐ ⟨ τ ⟩ᶠ (⟦ Γ''' ⟧ᵉᶠ f)
  ∎


split-env⁻¹-nat : ∀ {Γ Γ' Γ'' A B}
                → (p : Γ' , Γ'' split Γ)
                → (f : A →ᵐ B)
                →    ⟦ Γ ⟧ᵉᶠ f
                  ∘ᵐ split-env⁻¹ p
                ≡    split-env⁻¹ p
                  ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)

split-env⁻¹-nat {Γ} {Γ'} {Γ''} {A} {B} p f = 
  begin
       ⟦ Γ ⟧ᵉᶠ f
    ∘ᵐ split-env⁻¹ p
  ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
       idᵐ
    ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-congˡ (sym (split-env-split-env⁻¹-iso p)) ⟩
       (split-env⁻¹ p ∘ᵐ split-env p)
    ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
       split-env⁻¹ p
    ∘ᵐ split-env p
    ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-congʳ (sym (∘ᵐ-assoc _ _ _)) ⟩
       split-env⁻¹ p
    ∘ᵐ (   split-env p
        ∘ᵐ ⟦ Γ ⟧ᵉᶠ f)
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (split-env-nat p f))) ⟩
       split-env⁻¹ p
    ∘ᵐ (   ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
        ∘ᵐ split-env p)
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ⟩
       split-env⁻¹ p
    ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
    ∘ᵐ split-env p
    ∘ᵐ split-env⁻¹ p
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (split-env⁻¹-split-env-iso p)) ⟩
       split-env⁻¹ p
    ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
    ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-identityʳ _) ⟩
       split-env⁻¹ p
    ∘ᵐ ⟦ Γ'' ⟧ᵉᶠ (⟦ Γ' ⟧ᵉᶠ f)
  ∎
