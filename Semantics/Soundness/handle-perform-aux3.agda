-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform-aux3 (Mod : Model) where

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Substitutions
open import Syntax.EquationalTheory

open import Semantics.Interpretation Mod

open import Semantics.Renamings Mod
open import Semantics.Renamings.Properties.VC-rename Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Semantics.Soundness.handle-perform-aux4 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod


handle-perform-sound-aux3 : ∀ {Γ A B τ τ'} → (op : Op)
                          → (V : Γ ⊢V⦂ type-of-gtype (param op))
                          → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                          → (H : (op : Op) (τ'' : Time)
                               → Γ ∷ type-of-gtype (param op) ∷
                                  [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                                    ⊢C⦂ B ‼ (op-time op + τ''))
                          → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                          →   ×ᵐ-assoc⁻¹
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                                              ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                                              ∘ᵐ ×ᵐ-assoc
                                                                                              ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
                           ∘ᵐ ⟨ fstᵐ
                                ,
                                   ⟨ fstᵐ ∘ᵐ sndᵐ ,
                                        [ op-time op ]ᶠ (mapˣᵐ
                                                          (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                                  (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                                   ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                              ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                                             ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                                                          idᵐ)
                                     ∘ᵐ []-monoidal
                                     ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
                           ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                                           (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                                           (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                                                ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                                            ∘ᵐ []-monoidal
                                            ∘ᵐ mapˣᵐ δ idᵐ
                                            ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                                          ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
                           ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
                           ≡
                              mapˣᵐ (⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ) idᵐ
                           ∘ᵐ mapˣᵐ
                                idᵐ
                                ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapⁱˣᵐ (λ op →
                                                                           mapⁱˣᵐ (λ τ''' →
                                                                              (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                               ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                              ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                                          ∘ᵐ ×ᵐ-assoc⁻¹))))
                                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                                         ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                                           ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                                         ∘ᵐ mapˣᵐ idᵐ strᵀ
                                                         ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)))
                           ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ

handle-perform-sound-aux3 {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       ×ᵐ-assoc⁻¹
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                                                       ∘ᵐ ×ᵐ-assoc
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))))
    ∘ᵐ ⟨ fstᵐ
         ,
            ⟨ fstᵐ ∘ᵐ sndᵐ ,
                 [ op-time op ]ᶠ (mapˣᵐ
                                   (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                           (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                            ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                      ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                                   idᵐ)
              ∘ᵐ []-monoidal
              ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
      (cong₂ ⟨_,_⟩ᵐ
        (∘ᵐ-identityˡ _)
        (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
          (cong₂ ⟨_,_⟩ᵐ refl
            (sym (trans (∘ᵐ-congˡ ([]-∘ᵐ _ _)) (∘ᵐ-assoc _ _ _))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (   curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                          ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                          ∘ᵐ ×ᵐ-assoc
                                          ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op)))
                               ∘ᵐ mapˣᵐ
                                    (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                            (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                             ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                        ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                       ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                                    idᵐ)
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl
      (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (trans (sym (curryᵐ-nat _ _)) (cong curryᵐ
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) (⟦⟧ᵛ-⟦⟧ᵍ (arity op))
                                       ∘ᵐ mapˣᵐ
                                           (mapˣᵐ
                                             (⟨ op-time op ⟩ᶠ (   (mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                     (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                      ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                                 ∘ᵐ ×ᵐ-assoc⁻¹)))))
                                                                ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ))
                                             idᵐ)
                                           idᵐ))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl
      (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ
        (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym
          (trans (∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _))) (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _)) (sym
                (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                  (cong₂ mapˣᵐ (sym (ε-⟨⟩-nat _)) refl)))))
              (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _)))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ
                                            (mapˣᵐ
                                              (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                               ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                              idᵐ)
                                            idᵐ
                                       ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl
      (∘ᵐ-congˡ (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ
          (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (trans (sym (mapˣᵐ-∘ᵐ _ _ _ _))
                (cong₂ mapˣᵐ
                  (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ
                    (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → sym (⟨⟩ᵢᵐ-∘ᵐ _ _))))))
                      (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (trans
                        (cong ⟨_⟩ᵢᵐ (fun-ext (λ op → trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op))
                          (sym (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ op))
                            (trans (sym (⟨⟩ᵢᵐ-∘ᵐ _ _)) (trans (cong ⟨_⟩ᵢᵐ (fun-ext (λ τ''' →
                              trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ'''))
                                (trans (∘ᵐ-identityʳ _) (sym (trans (∘ᵐ-assoc _ _ _)
                                  (trans (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ τ''')) (trans (∘ᵐ-assoc _ _ _)
                                    (∘ᵐ-congʳ (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
                                      (sym (trans (cong curryᵐ (sym (∘ᵐ-assoc _ _ _))) (curryᵐ-nat _ _))))))))))))))
                              (⟨⟩ᵢᵐ-∘ᵐ _ _))))))))))
                      (⟨⟩ᵢᵐ-∘ᵐ _ _)))))
                  (∘ᵐ-identityˡ _)))
              (∘ᵐ-identityˡ _)) )))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ
                                            (mapˣᵐ
                                              (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                               ∘ᵐ ×ᵐ-assoc⁻¹
                                                                               ∘ᵐ mapˣᵐ ε-⟨⟩ idᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                              idᵐ)
                                            idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (cong₂ mapˣᵐ (cong₂ mapˣᵐ (∘ᵐ-congˡ (cong mapⁱˣᵐ (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext (λ τ''' →
          ∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congʳ (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _)) (sym
            (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
              (cong₂ ⟨_,_⟩ᵐ
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                  (sym (trans (sym (⟨⟩ᵐ-∘ᵐ _ _ _))
                    (cong₂ ⟨_,_⟩ᵐ
                      (⟨⟩ᵐ-fstᵐ _ _)
                      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                        (trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) (sym (∘ᵐ-identityˡ _)))))))))))
                (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-identityˡ _) (trans (⟨⟩ᵐ-sndᵐ _ _)
                  (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))))))))))))))))
              refl) refl))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ
                                            (mapˣᵐ
                                              (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                               ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                               ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                              idᵐ)
                                            idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (cong₂ ⟨_,_⟩ᵐ refl (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congˡ
      (cong [ op-time op ]ᶠ (cong curryᵐ (∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
        (trans (∘ᵐ-congˡ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (⟨⟩ᵐ-∘ᵐ _ _ _)))))
          (trans (∘ᵐ-congˡ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))) (sym (trans (sym (∘ᵐ-assoc _ _ _)) (trans (sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _)))
              (trans (sym (mapˣᵐ-⟨⟩ᵐ _ _ _ _))
                (cong₂ ⟨_,_⟩ᵐ
                  (sym (trans (∘ᵐ-identityˡ _) (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))))))))))
                  (trans (∘ᵐ-identityˡ _) (∘ᵐ-congʳ (sym
                    (⟨⟩ᵐ-unique _ _ _
                      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                        (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                          (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (∘ᵐ-congˡ (∘ᵐ-identityˡ _))))))))
                      (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) (trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))))))))))))))))))))))) ⟩
       ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ fstᵐ ,
         ⟨    (⟦⟧ᵍ-⟦⟧ᵛ (param op))
           ∘ᵐ fstᵐ
           ∘ᵐ sndᵐ ,
              [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ T-alg-of-handlerᵀ
                                       ∘ᵐ mapˣᵐ
                                            (   mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ''' →
                                                                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                                    ∘ᵐ curryᵐ (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                               ∘ᵐ mapˣᵐ (mapˣᵐ ε-⟨⟩ idᵐ) idᵐ
                                                                               ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                            idᵐ
                                       ∘ᵐ mapˣᵐ idᵐ (uncurryᵐ idᵐ)
                                       ∘ᵐ ×ᵐ-assoc
                                       ∘ᵐ mapˣᵐ idᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op))))
           ∘ᵐ []-monoidal
           ∘ᵐ ⟨ η⊣ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    (⟦⟧ᵛ-⟦⟧ᵍ (param op))
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ
                     ∘ᵐ mapˣᵐ idᵐ (   [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ))))
    ∘ᵐ ⟨ idᵐ , ⟨ ⟦ V ⟧ᵛᵗ , ⟨ η⊣ , η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ handle-perform-sound-aux4 {Γ} {A} {B} {τ} {τ'} op V M H N ⟩
       mapˣᵐ (⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ) idᵐ
    ∘ᵐ mapˣᵐ
         idᵐ
         ([ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                                ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ (ε-⟨⟩ ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ×ᵐ-assoc⁻¹))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ)))
    ∘ᵐ ⟨ idᵐ , η⊣ ⟩ᵐ
  ∎
