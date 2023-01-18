----------------------------------------
-- Interpretation of well-typed terms --
----------------------------------------

open import Semantics.Model

module Semantics.Interpretation (Mod : Model) where

open import Data.Empty

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Util.Equality
open import Util.Operations
open import Util.Time

open Model Mod

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → Obj
  ⟦ Base B ⟧ᵛ  = ConstObj B
  ⟦ Unit ⟧ᵛ    = 𝟙ᵐ
  ⟦ Empty ⟧ᵛ   = 𝟘ᵐ
  ⟦ A |×| B ⟧ᵛ = ⟦ A ⟧ᵛ ×ᵐ ⟦ B ⟧ᵛ
  ⟦ A ⇒ C ⟧ᵛ   = ⟦ A ⟧ᵛ ⇒ᵐ ⟦ C ⟧ᶜ
  ⟦ [ τ ] A ⟧ᵛ = [ τ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → Obj
  ⟦ A ‼ τ ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ τ

  infix 25 ⟦_⟧ᵛ
  infix 25 ⟦_⟧ᶜ

-- Relating the interpretation of ground types and ground type to type conversion

⟦⟧ᵛ-⟦⟧ᵍ : (B : GType) → ⟦ type-of-gtype B ⟧ᵛ →ᵐ ⟦ B ⟧ᵍ
⟦⟧ᵛ-⟦⟧ᵍ (Base B)   = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ Unit       = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ Empty      = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ (A |×|ᵍ B) = mapˣᵐ (⟦⟧ᵛ-⟦⟧ᵍ A) (⟦⟧ᵛ-⟦⟧ᵍ B)
⟦⟧ᵛ-⟦⟧ᵍ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)

⟦⟧ᵍ-⟦⟧ᵛ : (B : GType) → ⟦ B ⟧ᵍ →ᵐ ⟦ type-of-gtype B ⟧ᵛ
⟦⟧ᵍ-⟦⟧ᵛ (Base B)   = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ Unit       = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ Empty      = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ (A |×|ᵍ B) = mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ A) (⟦⟧ᵍ-⟦⟧ᵛ B)
⟦⟧ᵍ-⟦⟧ᵛ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)

⟦⟧ᵛ-⟦⟧ᵍ-iso : (B : GType)
            → ⟦⟧ᵍ-⟦⟧ᵛ B ∘ᵐ ⟦⟧ᵛ-⟦⟧ᵍ B ≡ idᵐ
⟦⟧ᵛ-⟦⟧ᵍ-iso (Base B) =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵛ-⟦⟧ᵍ-iso Unit =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵛ-⟦⟧ᵍ-iso Empty =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵛ-⟦⟧ᵍ-iso (A |×|ᵍ B) = 
  begin
       mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ A) (⟦⟧ᵍ-⟦⟧ᵛ B)
    ∘ᵐ mapˣᵐ (⟦⟧ᵛ-⟦⟧ᵍ A) (⟦⟧ᵛ-⟦⟧ᵍ B)
  ≡⟨ sym (mapˣᵐ-∘ᵐ _ _ _ _) ⟩
       mapˣᵐ
         (⟦⟧ᵍ-⟦⟧ᵛ A ∘ᵐ ⟦⟧ᵛ-⟦⟧ᵍ A)
         (⟦⟧ᵍ-⟦⟧ᵛ B ∘ᵐ ⟦⟧ᵛ-⟦⟧ᵍ B)
  ≡⟨ cong₂ mapˣᵐ (⟦⟧ᵛ-⟦⟧ᵍ-iso A) (⟦⟧ᵛ-⟦⟧ᵍ-iso B) ⟩
     mapˣᵐ idᵐ idᵐ
  ≡⟨ mapˣᵐ-identity ⟩
    idᵐ
  ∎
⟦⟧ᵛ-⟦⟧ᵍ-iso ([ τ ]ᵍ A) = 
  begin
       [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)
    ∘ᵐ [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)
  ≡⟨ sym ([]-∘ᵐ _ _) ⟩
    [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A ∘ᵐ ⟦⟧ᵛ-⟦⟧ᵍ A)
  ≡⟨ cong [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ-iso A) ⟩
    [ τ ]ᶠ idᵐ
  ≡⟨ []-idᵐ ⟩
    idᵐ
  ∎

⟦⟧ᵍ-⟦⟧ᵛ-iso : (B : GType)
            → ⟦⟧ᵛ-⟦⟧ᵍ B ∘ᵐ ⟦⟧ᵍ-⟦⟧ᵛ B ≡ idᵐ
⟦⟧ᵍ-⟦⟧ᵛ-iso (Base B) =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵍ-⟦⟧ᵛ-iso Unit =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵍ-⟦⟧ᵛ-iso Empty =
  begin
    idᵐ ∘ᵐ idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
    idᵐ
  ∎
⟦⟧ᵍ-⟦⟧ᵛ-iso (A |×|ᵍ B) = 
  begin
       mapˣᵐ (⟦⟧ᵛ-⟦⟧ᵍ A) (⟦⟧ᵛ-⟦⟧ᵍ B)
    ∘ᵐ mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ A) (⟦⟧ᵍ-⟦⟧ᵛ B)
  ≡⟨ sym (mapˣᵐ-∘ᵐ _ _ _ _) ⟩
       mapˣᵐ
         (⟦⟧ᵛ-⟦⟧ᵍ A ∘ᵐ ⟦⟧ᵍ-⟦⟧ᵛ A)
         (⟦⟧ᵛ-⟦⟧ᵍ B ∘ᵐ ⟦⟧ᵍ-⟦⟧ᵛ B)
  ≡⟨ cong₂ mapˣᵐ (⟦⟧ᵍ-⟦⟧ᵛ-iso A) (⟦⟧ᵍ-⟦⟧ᵛ-iso B) ⟩
     mapˣᵐ idᵐ idᵐ
  ≡⟨ mapˣᵐ-identity ⟩
    idᵐ
  ∎
⟦⟧ᵍ-⟦⟧ᵛ-iso ([ τ ]ᵍ A) =
  begin
       [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)
    ∘ᵐ [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)
  ≡⟨ sym ([]-∘ᵐ _ _) ⟩
    [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A ∘ᵐ ⟦⟧ᵍ-⟦⟧ᵛ A)
  ≡⟨ cong [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ-iso A) ⟩
    [ τ ]ᶠ idᵐ
  ≡⟨ []-idᵐ ⟩
    idᵐ
  ∎


-- Interpretation of contexts as functors

⟦_⟧ᵉᵒ : Ctx → Obj → Obj
⟦ [] ⟧ᵉᵒ      B = B
⟦ Γ ∷ A ⟧ᵉᵒ   B = ⟦ Γ ⟧ᵉᵒ B ×ᵐ ⟦ A ⟧ᵛ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᵒ B = ⟨ τ ⟩ᵒ (⟦ Γ ⟧ᵉᵒ B)

⟦_⟧ᵉᶠ : ∀ {A B} → (Γ : Ctx) → A →ᵐ B → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟦ Γ ⟧ᵉᵒ B
⟦ [] ⟧ᵉᶠ      f = f
⟦ Γ ∷ A ⟧ᵉᶠ   f = mapˣᵐ (⟦ Γ ⟧ᵉᶠ f) idᵐ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᶠ f = ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)

⟦⟧ᵉ-idᵐ : ∀ {Γ A} → ⟦ Γ ⟧ᵉᶠ (idᵐ {A = A}) ≡ idᵐ
⟦⟧ᵉ-idᵐ {[]} =
  begin
    idᵐ
  ≡⟨⟩
    idᵐ
  ∎
⟦⟧ᵉ-idᵐ {Γ ∷ A} =
  begin
    ⟨ ⟦ Γ ⟧ᵉᶠ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (begin
         fstᵐ ∘ᵐ idᵐ
       ≡⟨ ∘ᵐ-identityʳ _ ⟩
         fstᵐ
       ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
         idᵐ ∘ᵐ fstᵐ
       ≡⟨ ∘ᵐ-congˡ (sym (⟦⟧ᵉ-idᵐ {Γ})) ⟩
         ⟦ Γ ⟧ᵉᶠ idᵐ ∘ᵐ fstᵐ
       ∎)
       (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))) ⟩
    idᵐ
  ∎
⟦⟧ᵉ-idᵐ {Γ ⟨ τ ⟩} = 
  begin
    ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ idᵐ)
  ≡⟨ cong ⟨ τ ⟩ᶠ (⟦⟧ᵉ-idᵐ {Γ}) ⟩
    ⟨ τ ⟩ᶠ idᵐ
  ≡⟨ ⟨⟩-idᵐ ⟩
    idᵐ
  ∎

⟦⟧ᵉ-∘ᵐ : ∀ {Γ A B C} → (g : B →ᵐ C) → (f : A →ᵐ B)
       → ⟦ Γ ⟧ᵉᶠ (g ∘ᵐ f) ≡ ⟦ Γ ⟧ᵉᶠ g ∘ᵐ ⟦ Γ ⟧ᵉᶠ f
⟦⟧ᵉ-∘ᵐ {[]} g f = 
  begin
    g ∘ᵐ f
  ≡⟨⟩
    g ∘ᵐ f
  ∎
⟦⟧ᵉ-∘ᵐ {Γ ∷ A} g f = 
  begin
    ⟨ ⟦ Γ ⟧ᵉᶠ (g ∘ᵐ f) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
       (∘ᵐ-congˡ (⟦⟧ᵉ-∘ᵐ {Γ} g f))
       (∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _))) ⟩
    ⟨ (⟦ Γ ⟧ᵉᶠ g ∘ᵐ ⟦ Γ ⟧ᵉᶠ f) ∘ᵐ fstᵐ , (idᵐ ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ mapˣᵐ-∘ᵐ _ _ _ _ ⟩
       ⟨ ⟦ Γ ⟧ᵉᶠ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟦ Γ ⟧ᵉᶠ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ∎
⟦⟧ᵉ-∘ᵐ {Γ ⟨ τ ⟩} g f = 
  begin
    ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ (g ∘ᵐ f))
  ≡⟨ cong ⟨ τ ⟩ᶠ (⟦⟧ᵉ-∘ᵐ {Γ} g f) ⟩
    ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ g ∘ᵐ ⟦ Γ ⟧ᵉᶠ f)
  ≡⟨ ⟨⟩-∘ᵐ _ _ ⟩
    ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ g) ∘ᵐ ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)
  ∎

-- Environments are such functors applied to the terminal object

⟦_⟧ᵉ : Ctx → Obj
⟦ Γ ⟧ᵉ = ⟦ Γ ⟧ᵉᵒ 𝟙ᵐ

infix 25 ⟦_⟧ᵉ

-- Splitting an environment according to context splitting

split-env : ∀ {Γ Γ' Γ''}
          → Γ' , Γ'' split Γ
          → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟦ Γ'' ⟧ᵉᵒ (⟦ Γ' ⟧ᵉᵒ A)
          
split-env split-[]             = idᵐ
split-env (split-∷ p)          = mapˣᵐ (split-env p) idᵐ
split-env (split-⟨⟩ {τ = τ} p) = ⟨ τ ⟩ᶠ (split-env p)

split-env⁻¹ : ∀ {Γ Γ' Γ''}
            → Γ' , Γ'' split Γ
            → ∀ {A} → ⟦ Γ'' ⟧ᵉᵒ (⟦ Γ' ⟧ᵉᵒ A) →ᵐ ⟦ Γ ⟧ᵉᵒ A

split-env⁻¹ split-[]             = idᵐ
split-env⁻¹ (split-∷ p)          = mapˣᵐ (split-env⁻¹ p) idᵐ
split-env⁻¹ (split-⟨⟩ {τ = τ} p) = ⟨ τ ⟩ᶠ (split-env⁻¹ p)

-- Interaction of ⟨_⟩ modality and the time-travelling operation on contexts
--
-- This is a semantic counterpart to the PRA situation between (-) ⟨ τ ⟩
-- and (-) -ᶜ τ witnessed by the renamings η-PRA-ren and ε-PRA-ren.

η-PRA : ∀ {Γ A}
      → (τ : Time)
      → τ ≤ ctx-time Γ
      → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟨ τ ⟩ᵒ (⟦ Γ -ᶜ τ ⟧ᵉᵒ A)
         
η-PRA {Γ} zero p =
  η
η-PRA {Γ ∷ B} (suc τ) p =
     η-PRA {Γ} (suc τ) p
  ∘ᵐ fstᵐ
η-PRA {Γ ⟨ τ' ⟩} (suc τ) p with suc τ ≤? τ'
... | yes q =
     μ⁻¹
  ∘ᵐ ⟨⟩-≤ (≤-reflexive (m+[n∸m]≡n q))
... | no ¬q =
     ⟨⟩-≤ (m≤n+m∸n (suc τ) τ')
  ∘ᵐ μ
  ∘ᵐ ⟨ τ' ⟩ᶠ (η-PRA {Γ} (suc τ ∸ τ')
       (≤-trans
         (∸-monoˡ-≤ τ' p)
         (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))

ε-PRA : ∀ {Γ A}
      → (τ : Time)
      → ⟦ Γ ⟨ τ ⟩ -ᶜ τ ⟧ᵉᵒ A →ᵐ ⟦ Γ ⟧ᵉᵒ A

ε-PRA {Γ} zero =
  η⁻¹
ε-PRA {Γ} (suc τ) with suc τ ≤? suc τ
... | yes p =
  η⁻¹ ∘ᵐ
  ⟨⟩-≤ (≤-reflexive (sym (n∸n≡0 τ)))
... | no ¬p =
  ⊥-elim (¬p ≤-refl)

-- Projecting a variable out of an environment

var-in-env : ∀ {Γ A τ} → (x : A ∈[ τ ] Γ) → ⟦ Γ ⟧ᵉ →ᵐ ⟦ A ⟧ᵛ
var-in-env Hd = sndᵐ
var-in-env (Tl-∷ x) = var-in-env x ∘ᵐ fstᵐ
var-in-env (Tl-⟨⟩ {τ = τ} x) = ε-⟨⟩ ∘ᵐ ⟨ τ ⟩ᶠ (var-in-env x)

-- Interpretation of well-typed value and computation terms

mutual

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → Γ ⊢V⦂ A → ⟦ Γ ⟧ᵉ →ᵐ ⟦ A ⟧ᵛ
  
  ⟦ var x ⟧ᵛᵗ = var-in-env x
  
  ⟦ const c ⟧ᵛᵗ = constᵐ c ∘ᵐ terminalᵐ
  
  ⟦ ⋆ ⟧ᵛᵗ = terminalᵐ

  ⟦ ⦉ V , W ⦊ ⟧ᵛᵗ = ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  
  ⟦ lam M ⟧ᵛᵗ = curryᵐ ⟦ M ⟧ᶜᵗ
  
  ⟦ box {τ = τ} V ⟧ᵛᵗ = [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣ 

  infix 25 ⟦_⟧ᵛᵗ


  ⟦_⟧ᶜᵗ : ∀ {Γ C} → Γ ⊢C⦂ C → ⟦ Γ ⟧ᵉ →ᵐ ⟦ C ⟧ᶜ
  
  ⟦ return V ⟧ᶜᵗ = ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (_;_ {τ = τ} M N) =
    μᵀ
    ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵐ strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ}
    ∘ᵐ ⟨ η⊣ {⟦ Γ ⟧ᵉ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ
        
  ⟦ V · W ⟧ᶜᵗ = appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ

  ⟦_⟧ᶜᵗ {Γ} (match V `in M) =
       ⟦ M ⟧ᶜᵗ
    ∘ᵐ ×ᵐ-assoc⁻¹
    ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
  
  ⟦ absurd V ⟧ᶜᵗ = initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {τ} op V M) =
    let f : ⟦ Γ ⟧ᵉ →ᵐ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
        f = [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ) ∘ᵐ η⊣ in
    let g : [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
         →ᵐ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
        g = [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) (idᵐ {Tᵒ ⟦ A ⟧ᵛ τ})) in
    opᵀ op ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ , g ∘ᵐ f ⟩ᵐ

  ⟦ delay τ M ⟧ᶜᵗ =
       delayᵀ τ
    ∘ᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ)
    ∘ᵐ η⊣ 

  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    let f : ⟦ Γ ⟧ᵉ →ᵐ Πᵐ Op (λ op → Πᵐ Time (λ τ'' → ⟦ Γ ⟧ᵉ))
        f = ⟨ (λ op → ⟨ (λ τ'' → idᵐ) ⟩ᵢᵐ) ⟩ᵢᵐ in
    let g : (op : Op) → (τ'' : Time)
          → ⟦ type-of-gtype (param op) ⟧ᵛ ×ᵐ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ
              ⇒ᵐ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵐ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
          →ᵐ ⟦ param op ⟧ᵍ ×ᵐ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ
              ⇒ᵐ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵐ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
        g = λ op τ'' →
               map⇒ᵐ
                 (mapˣᵐ
                   (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                   ([ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) (idᵐ {Tᵒ ⟦ B ⟧ᵛ τ''}))))
                 (idᵐ {Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')}) in
       uncurryᵐ (
            T-alg-of-handlerᵀ
         ∘ᵐ mapⁱˣᵐ (λ op → mapⁱˣᵐ (λ τ'' →
              g op τ'' ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc⁻¹)))
         ∘ᵐ f)
    ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ mapˣᵐ idᵐ (strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ})
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ = τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ

  ⟦ unbox {τ = τ} p V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ ,
                    ε⊣ {τ = τ}
                 ∘ᵐ (⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ)
                 ∘ᵐ η-PRA τ p ⟩ᵐ
    
  infix 25 ⟦_⟧ᶜᵗ


