-------------------------------------
-- Soundness of the interpretation --
-------------------------------------

open import Semantics.Model

module Semantics.Soundness.handle-perform (Mod : Model) where

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
open import Semantics.Renamings.Properties.η-ᶜ-ren-decompose Mod

open import Semantics.Substitutions.Properties.VC-subst Mod

open import Semantics.Interpretation.Properties.τ-subst Mod

open import Semantics.Soundness.handle-perform-aux Mod
open import Semantics.Soundness.handle-perform-aux9 Mod

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

handle-perform-sound : ∀ {Γ A B τ τ'} → (op : Op)
                     → (V : Γ ⊢V⦂ type-of-gtype (param op))
                     → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
                     → (H : (op : Op) (τ'' : Time)
                          → Γ ∷ type-of-gtype (param op) ∷
                             [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                               ⊢C⦂ B ‼ (op-time op + τ''))
                     → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
                     → ⟦ handle perform op V M `with H `in N ⟧ᶜᵗ
                     ≡ ⟦ τ-subst (sym (+-assoc (op-time op) τ τ'))
                           ((H op (τ + τ') [ Tl-∷ Hd ↦ V ]c)
                              [ Hd ↦ box (lam (handle M
                                               `with (λ op' τ'' → C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren ∘ʳ id-ren)))
                                                                    (H op' τ''))
                                               `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N))) ]c) ⟧ᶜᵗ

handle-perform-sound {Γ} {A} {B} {τ} {τ'} op V M H N =
  begin
       uncurryᵐ (   T-alg-of-handlerᵀ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' →
                          (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                           ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))
                       ∘ᵐ projᵐ τ''') ⟩ᵢᵐ
                    ∘ᵐ projᵐ op) ⟩ᵢᵐ
                 ∘ᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , strᵀ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                    opᵀ op
                 ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                         [ op-time op ]ᶠ (curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , ⟦⟧ᵍ-⟦⟧ᵛ (arity op) ∘ᵐ sndᵐ ⟩ᵐ))
                      ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ) ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ handle-perform-sound-aux9 {Γ} {A} {B} {τ} {τ'} op V M H N ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ (  mapˣᵐ (curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                         ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))) idᵐ
       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                         ∘ᵐ ×ᵐ-assoc))))
       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
       ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
       ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
       ∘ᵐ ⟨ idᵐ
            ,
               mapˣᵐ
                 (mapⁱˣᵐ (λ op →
                    mapⁱˣᵐ (λ τ''' →
                      (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                       ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
                 idᵐ
            ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ (curryᵐ (   (⟦ H op (τ + τ') ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                      ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))))) idᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (trans (sym (∘ᵐ-assoc _ _ _)) (trans (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _)))
      (trans (∘ᵐ-congˡ (trans (cong uncurryᵐ (∘ᵐ-identityˡ _)) (curryᵐ-uncurryᵐ-iso _)))
        (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-assoc _ _ _))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') ⟧ᶜᵗ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ fstᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (uncurryᵐ T-alg-of-handlerᵀ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (curryᵐ (   mapˣᵐ idᵐ appᵐ
                                                      ∘ᵐ ×ᵐ-assoc))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (mapˣᵐ ε-⟨⟩ idᵐ)))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ []-monoidal)
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ (mapˣᵐ η⊣ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ
         ,
            mapˣᵐ
              (mapⁱˣᵐ (λ op →
                 mapⁱˣᵐ (λ τ''' →
                   (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                    ∘ᵐ curryᵐ (⟦ H op τ''' ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ)))))
              idᵐ
         ∘ᵐ mapˣᵐ ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ idᵐ ⟩ᵐ
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ ([ op-time op ]ᶠ (map⇒ᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ))))
    ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ
                    idᵐ
                    (   [ op-time op ]ᶠ (   map⇒ᵐ idᵐ strᵀ
                                         ∘ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
                     ∘ᵐ []-monoidal
                     ∘ᵐ mapˣᵐ δ idᵐ))
    ∘ᵐ mapˣᵐ idᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ ,
                 ⟨    ⟦⟧ᵛ-⟦⟧ᵍ (param op)
                   ∘ᵐ ⟦ V ⟧ᵛᵗ ,
                      [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) idᵐ)
                   ∘ᵐ [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ)
                   ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (handle-perform-sound-aux {Γ} {A} {B} {τ} {τ'} op V M H N)) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ (   ⟦ N ⟧ᶜᵗ
                                                    ∘ᵐ mapˣᵐ ((⟨⟩-≤ (≤-reflexive (+-comm (op-time op) τ)) ∘ᵐ μ) ∘ᵐ ⟨ τ ⟩ᶠ fstᵐ) idᵐ))
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
      (cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong (mapˣᵐ idᵐ) (cong Tᶠ
        (sym (C-rename≡∘ᵐ (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N)))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   (   ⟦ H op τ''' ⟧ᶜᵗ
                                                                       ∘ᵐ mapˣᵐ (mapˣᵐ ((idᵐ ∘ᵐ ε-⟨⟩) ∘ᵐ fstᵐ) idᵐ) idᵐ)
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren (wk-ren {A = type-of-gtype (arity op)}) ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong ⟨ idᵐ ,_⟩ᵐ (∘ᵐ-congˡ (cong [ op-time op ]ᶠ
      (cong curryᵐ (∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong mapⁱˣᵐ (fun-ext (λ op → cong mapⁱˣᵐ (fun-ext λ τ''' →
        ∘ᵐ-congʳ (cong curryᵐ (∘ᵐ-congˡ (sym (C-rename≡∘ᵐ
                                               (cong-∷-ren (cong-∷-ren
                                                  (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren)))
                                               (H op τ'''))))))))))))))))))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren
                                                                          (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren))) (H op τ''') ⟧ᶜᵗ
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ (   ⟦ H op (τ + τ') ⟧ᶜᵗ
        ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren
                                                                          (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren))) (H op τ''') ⟧ᶜᵗ
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congˡ (sym (C-subst≡∘ᵐ (H op (τ + τ')) (Tl-∷ Hd) V ))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') [ Tl-∷ Hd ↦ V ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren
                                                                          (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren))) (H op τ''') ⟧ᶜᵗ
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityʳ _))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') [ Tl-∷ Hd ↦ V ]c ⟧ᶜᵗ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren
                                                                          (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren))) (H op τ''') ⟧ᶜᵗ
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
      ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _))) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ H op (τ + τ') [ Tl-∷ Hd ↦ V ]c ⟧ᶜᵗ
    ∘ᵐ idᵐ
    ∘ᵐ ⟨ idᵐ ,
         [ op-time op ]ᶠ (curryᵐ (   uncurryᵐ (   T-alg-of-handlerᵀ
                                               ∘ᵐ mapⁱˣᵐ (λ op →
                                                    mapⁱˣᵐ (λ τ''' →
                                                       (   map⇒ᵐ (mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ (param op)) ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) idᵐ))) idᵐ
                                                        ∘ᵐ curryᵐ (   ⟦ C-rename (cong-∷-ren (cong-∷-ren
                                                                          (wk-ren ∘ʳ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η⁻¹-ren) ∘ʳ id-ren))) (H op τ''') ⟧ᶜᵗ
                                                                   ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ))))
                                               ∘ᵐ ⟨ (λ op → ⟨ (λ τ''' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ)
                                  ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N ⟧ᶜᵗ)
                                  ∘ᵐ mapˣᵐ idᵐ strᵀ
                                  ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ))
         ∘ᵐ η⊣ ⟩ᵐ
      ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (C-subst≡∘ᵐ (H op (τ + τ') [ Tl-∷ Hd ↦ V ]c) _ _)) ⟩
       τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
    ∘ᵐ ⟦ (H op (τ + τ') [ Tl-∷ Hd ↦ V ]c)
           [ Hd ↦ box (lam (handle M
                            `with (λ op' τ'' → C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren ∘ʳ id-ren)))
                                                 (H op' τ''))
                            `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N))) ]c ⟧ᶜᵗ
  ≡⟨ sym (⟦τ-subst⟧≡τ-substᵀ (sym (+-assoc (op-time op) τ τ')) _) ⟩
    ⟦ τ-subst (sym (+-assoc (op-time op) τ τ'))
        ((H op (τ + τ') [ Tl-∷ Hd ↦ V ]c)
           [ Hd ↦ box (lam (handle M
                            `with (λ op' τ'' → C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren ∘ʳ id-ren)))
                                                 (H op' τ''))
                            `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren)) N))) ]c) ⟧ᶜᵗ
  ∎
