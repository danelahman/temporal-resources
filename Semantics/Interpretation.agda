-------------------------------------------------------------
-- Interpretation of well-typed terms in time-varying sets --
-------------------------------------------------------------

open import Semantics.Model

module Semantics.Interpretation (Mod : Model) where

open import Relation.Nullary

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Util.Operations
open import Util.Time

open Model Mod

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → Obj
  ⟦ Base B ⟧ᵛ  = ConstObj B
  ⟦ Unit ⟧ᵛ    = 𝟙ᵐ
  ⟦ Empty ⟧ᵛ   = 𝟘ᵐ
  ⟦ A ⇒ C ⟧ᵛ   = ⟦ A ⟧ᵛ ⇒ᵐ ⟦ C ⟧ᶜ
  ⟦ [ τ ] A ⟧ᵛ = [ τ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → Obj
  ⟦ A ‼ τ ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ τ

  infix 25 ⟦_⟧ᵛ
  infix 25 ⟦_⟧ᶜ

-- Relating the interpretation of ground types and ground type to type conversion

⟦⟧ᵛ-⟦⟧ᵍ : (B : GType) → ⟦ type-of-gtype B ⟧ᵛ →ᵐ ⟦ B ⟧ᵍ
⟦⟧ᵛ-⟦⟧ᵍ (Base B) = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ Unit     = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ Empty    = idᵐ
⟦⟧ᵛ-⟦⟧ᵍ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)

⟦⟧ᵍ-⟦⟧ᵛ : (B : GType) → ⟦ B ⟧ᵍ →ᵐ ⟦ type-of-gtype B ⟧ᵛ
⟦⟧ᵍ-⟦⟧ᵛ (Base B) = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ Unit     = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ Empty    = idᵐ
⟦⟧ᵍ-⟦⟧ᵛ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)

-- Interpretation of contexts as functors

⟦_⟧ᵉᵒ : Ctx → Obj → Obj
⟦ [] ⟧ᵉᵒ      B = B
⟦ Γ ∷ A ⟧ᵉᵒ   B = ⟦ Γ ⟧ᵉᵒ B ×ᵐ ⟦ A ⟧ᵛ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᵒ B = ⟨ τ ⟩ᵒ (⟦ Γ ⟧ᵉᵒ B)

⟦_⟧ᵉᶠ : ∀ {A B} → (Γ : Ctx) → A →ᵐ B → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟦ Γ ⟧ᵉᵒ B
⟦ [] ⟧ᵉᶠ      f = f
⟦ Γ ∷ A ⟧ᵉᶠ   f = mapˣᵐ (⟦ Γ ⟧ᵉᶠ f) idᵐ
⟦ Γ ⟨ τ ⟩ ⟧ᵉᶠ f = ⟨ τ ⟩ᶠ (⟦ Γ ⟧ᵉᶠ f)

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

-- Total time-passage of an environment as a single ⟨_⟩ modality

env-ctx-time-⟨⟩ : (Γ : Ctx)
                → ∀ {A} → ⟦ Γ ⟧ᵉᵒ A →ᵐ ⟨ ctx-time Γ ⟩ᵒ A

env-ctx-time-⟨⟩ []        = η
env-ctx-time-⟨⟩ (Γ ∷ A)   = env-ctx-time-⟨⟩ Γ ∘ᵐ fstᵐ
env-ctx-time-⟨⟩ (Γ ⟨ τ ⟩) {A} =
     ⟨⟩-≤ {A} (≤-reflexive (+-comm (ctx-time Γ) τ))
  ∘ᵐ μ {A}
  ∘ᵐ ⟨ τ ⟩ᶠ (env-ctx-time-⟨⟩ Γ)

-- Interaction of ⟨_⟩ modality and the time-travelling operation on contexts

env-⟨⟩-ᶜ : ∀ {Γ}
         → (τ : Time) → τ ≤ ctx-time Γ
         → ⟦ Γ ⟧ᵉ →ᵐ ⟨ τ ⟩ᵒ (⟦ Γ -ᶜ τ ⟧ᵉ)
         
env-⟨⟩-ᶜ {Γ} zero p =
  η
env-⟨⟩-ᶜ {Γ ∷ B} (suc τ) p =
     env-⟨⟩-ᶜ {Γ} (suc τ) p
  ∘ᵐ fstᵐ
env-⟨⟩-ᶜ {Γ ⟨ τ' ⟩} (suc τ) p with suc τ ≤? τ'
... | yes q =
     μ⁻¹ {⟦ Γ ⟧ᵉ} {suc τ} {τ' ∸ suc τ}
  ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᵉ} (≤-reflexive (m+[n∸m]≡n q))
... | no ¬q =
     ⟨⟩-≤ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} (m≤n+m∸n (suc τ) τ')
  ∘ᵐ μ {⟦ Γ -ᶜ (suc τ ∸ τ') ⟧ᵉ} {τ'} {suc τ ∸ τ'}
  ∘ᵐ ⟨ τ' ⟩ᶠ (env-⟨⟩-ᶜ {Γ} (suc τ ∸ τ')
       (≤-trans
         (∸-monoˡ-≤ τ' p)
         (≤-reflexive (m+n∸n≡m (ctx-time Γ) τ'))))

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
  
  ⟦ absurd V ⟧ᶜᵗ = initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {τ} op V M) =
    let f : ⟦ Γ ⟧ᵉ →ᵐ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
        f = [ op-time op ]ᶠ (curryᵐ ⟦ M ⟧ᶜᵗ) ∘ᵐ η⊣ in
    let g : [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
         →ᵐ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ τ)
        g = [ op-time op ]ᶠ (map⇒ᵐ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) (idᵐ {Tᵒ ⟦ A ⟧ᵛ τ})) in
    opᵀ op ∘ᵐ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵐ ⟦ V ⟧ᵛᵗ , g ∘ᵐ f ⟩ᵐ

  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    let f : ⟦ Γ ⟧ᵉ →ᵐ Π Op (λ op → Π Time (λ τ'' → ⟦ Γ ⟧ᵉ))
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
              g op τ'' ∘ᵐ curryᵐ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵐ ×ᵐ-assoc)))
         ∘ᵐ f)
    ∘ᵐ mapˣᵐ idᵐ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵐ mapˣᵐ idᵐ (strᵀ {⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ})
    ∘ᵐ ⟨ idᵐ , ⟨ η⊣ {⟦ Γ ⟧ᵉ} {τ = τ} , ⟦ M ⟧ᶜᵗ ⟩ᵐ ⟩ᵐ

  ⟦ unbox {τ = τ} p V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ ,
                    ε⊣ {τ = τ}
                 ∘ᵐ (⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ)
                 ∘ᵐ env-⟨⟩-ᶜ τ p ⟩ᵐ

  ⟦ delay τ M ⟧ᶜᵗ =
       delayᵀ τ
    ∘ᵐ ([ τ ]ᶠ ⟦ M ⟧ᶜᵗ)
    ∘ᵐ η⊣ 
    
  infix 25 ⟦_⟧ᶜᵗ

