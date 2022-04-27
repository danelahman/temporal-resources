-------------------------------------------------------------
-- Interpretation of well-typed terms in time-varying sets --
-------------------------------------------------------------

open import Function

open import Data.Product

open import Syntax.Types
open import Syntax.Contexts
open import Syntax.Language

open import Semantics.TSets
open import Semantics.Monad

open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Modality.Adjunction

open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Interpretation where

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → TSet
  ⟦ Base B ⟧ᵛ  = ConstTSet (BaseSet B)
  ⟦ Unit ⟧ᵛ    = 𝟙ᵗ
  ⟦ Empty ⟧ᵛ   = 𝟘ᵗ
  ⟦ A ⇒ C ⟧ᵛ   = ⟦ A ⟧ᵛ ⇒ᵗ ⟦ C ⟧ᶜ
  ⟦ [ τ ] A ⟧ᵛ = [ τ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → TSet
  ⟦ A ‼ τ ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ τ

  infix 25 ⟦_⟧ᵛ
  infix 25 ⟦_⟧ᶜ

-- Relating the interpretation of ground types and ground type to type conversion

⟦⟧ᵛ-⟦⟧ᵍ : (B : GType) → ⟦ type-of-gtype B ⟧ᵛ →ᵗ ⟦ B ⟧ᵍ
⟦⟧ᵛ-⟦⟧ᵍ (Base B) = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Unit     = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ Empty    = idᵗ
⟦⟧ᵛ-⟦⟧ᵍ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵛ-⟦⟧ᵍ A)

⟦⟧ᵍ-⟦⟧ᵛ : (B : GType) → ⟦ B ⟧ᵍ →ᵗ ⟦ type-of-gtype B ⟧ᵛ
⟦⟧ᵍ-⟦⟧ᵛ (Base B) = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Unit     = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ Empty    = idᵗ
⟦⟧ᵍ-⟦⟧ᵛ ([ τ ]ᵍ A) = [ τ ]ᶠ (⟦⟧ᵍ-⟦⟧ᵛ A)

-- Interpretation of contexts as environments

⟦_⟧ᵉ : Ctx → TSet
⟦ [] ⟧ᵉ      = 𝟙ᵗ
⟦ Γ ∷ A ⟧ᵉ   = ⟦ Γ ⟧ᵉ ×ᵗ ⟦ A ⟧ᵛ
⟦ Γ ⟨ τ ⟩ ⟧ᵉ = ⟨ τ ⟩ᵒ ⟦ Γ ⟧ᵉ

infix 25 ⟦_⟧ᵉ

-- Total time-passage of an environment as a single ⟨_⟩ modality

split-env-⟨⟩ : ∀ {Γ Γ' Γ''} → Γ' , Γ'' split Γ → ⟦ Γ ⟧ᵉ →ᵗ ⟨ ctx-time Γ'' ⟩ᵒ ⟦ Γ' ⟧ᵉ
split-env-⟨⟩ split-[]    = η
split-env-⟨⟩ (split-∷ p) = split-env-⟨⟩ p ∘ᵗ fstᵗ
split-env-⟨⟩ {Γ' = Γ'} {Γ'' = Γ'' ⟨ τ ⟩} (split-⟨⟩ p) =
     ⟨⟩-≤ {A = ⟦ Γ' ⟧ᵉ} (≤-reflexive (+-comm (ctx-time Γ'') τ))
  ∘ᵗ μ {A = ⟦ Γ' ⟧ᵉ}
  ∘ᵗ ⟨ τ ⟩ᶠ (split-env-⟨⟩ p)

-- Projecting a variable out of an environment

var-in-env : ∀ {Γ A τ} → A ∈[ τ ] Γ → ⟦ Γ ⟧ᵉ →ᵗ ⟨ τ ⟩ᵒ ⟦ A ⟧ᵛ
var-in-env {A = A} Hd                = η ∘ᵗ sndᵗ
var-in-env {A = A} (Tl-∷ x)          = var-in-env x ∘ᵗ fstᵗ
var-in-env {A = A} (Tl-⟨⟩ {τ = τ} x) = μ {A = ⟦ A ⟧ᵛ} ∘ᵗ ⟨ τ ⟩ᶠ (var-in-env x)

-- Semantic constants for base-typed value constants

constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ ConstTSet (BaseSet B)
constᵗ c = tset-map (λ _ → c) (λ _ _ → refl)

-- Interpretation of temporal contexts as functors in terms of [_] and ⟨_⟩ modalities

[_]ᵗᵒ : (τs : TCtx) → TSet → TSet
[ ⦉ τ ⦊ ]ᵗᵒ A = [ τ ]ᵒ A
[ τs ⟨ τ ⟩ ]ᵗᵒ A = [ τs ]ᵗᵒ ([ τ ]ᵒ A)

[_]ᵗᶠ : ∀ {A B} → (τs : TCtx) → A →ᵗ B → [ τs ]ᵗᵒ A →ᵗ [ τs ]ᵗᵒ B
[ ⦉ τ ⦊ ]ᵗᶠ f = [ τ ]ᶠ f
[ τs ⟨ τ ⟩ ]ᵗᶠ f = [ τs ]ᵗᶠ ([ τ ]ᶠ f)

⟨_⟩ᵗᵒ : (τs : TCtx) → TSet → TSet
⟨ ⦉ τ ⦊ ⟩ᵗᵒ A = ⟨ τ ⟩ᵒ A
⟨ τs ⟨ τ ⟩ ⟩ᵗᵒ A = ⟨ τ ⟩ᵒ (⟨ τs ⟩ᵗᵒ A)

⟨_⟩ᵗᶠ : ∀ {A B} → (τs : TCtx) → A →ᵗ B → ⟨ τs ⟩ᵗᵒ A →ᵗ ⟨ τs ⟩ᵗᵒ B
⟨ ⦉ τ ⦊ ⟩ᵗᶠ f = ⟨ τ ⟩ᶠ f
⟨ τs ⟨ τ ⟩ ⟩ᵗᶠ f = ⟨ τ ⟩ᶠ (⟨ τs ⟩ᵗᶠ f)

η-⊣-tctx : ∀ {A τs} → A →ᵗ [ τs ]ᵗᵒ (⟨ τs ⟩ᵗᵒ A)
η-⊣-tctx {τs = ⦉ τ ⦊} = η-⊣
η-⊣-tctx {τs = τs ⟨ τ ⟩} = [ τs ]ᵗᶠ η-⊣ ∘ᵗ η-⊣-tctx {τs = τs}

T-[]-tctx-module : ∀ {A τs τ'} → [ τs ]ᵗᵒ (Tᵒ A τ') →ᵗ Tᵒ A (tctx-time τs + τ')
T-[]-tctx-module {τs = ⦉ τ ⦊} = T-[]-module
T-[]-tctx-module {τs = τs ⟨ τ ⟩} =
     T-≤τ (≤-reflexive (sym (+-assoc (tctx-time τs) τ _)))
  ∘ᵗ T-[]-tctx-module {τs = τs}
  ∘ᵗ [ τs ]ᵗᶠ T-[]-module

⟨⟩-tctx-++ᶜ : ∀ {Γ} → (τs : TCtx) → ⟨ τs ⟩ᵗᵒ ⟦ Γ ⟧ᵉ →ᵗ ⟦ Γ ++ᶜ tctx-ctx τs ⟧ᵉ
⟨⟩-tctx-++ᶜ ⦉ τ ⦊ = idᵗ
⟨⟩-tctx-++ᶜ (τs ⟨ τ ⟩) = ⟨ τ ⟩ᶠ (⟨⟩-tctx-++ᶜ τs)

-- Interpretation of well-typed value and computation terms

mutual

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → Γ ⊢V⦂ A → ⟦ Γ ⟧ᵉ →ᵗ ⟦ A ⟧ᵛ
  
  ⟦ var x ⟧ᵛᵗ = ε-⟨⟩ ∘ᵗ var-in-env x
  
  ⟦ const c ⟧ᵛᵗ = constᵗ c ∘ᵗ terminalᵗ
  
  ⟦ ⋆ ⟧ᵛᵗ = terminalᵗ
  
  ⟦ lam M ⟧ᵛᵗ = curryᵗ ⟦ M ⟧ᶜᵗ
  
  ⟦ box {τ = τ} V ⟧ᵛᵗ = [ τ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵗ η-⊣ 

  infix 25 ⟦_⟧ᵛᵗ


  ⟦_⟧ᶜᵗ : ∀ {Γ C} → Γ ⊢C⦂ C → ⟦ Γ ⟧ᵉ →ᵗ ⟦ C ⟧ᶜ
  
  ⟦ return V ⟧ᶜᵗ = ηᵀ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (_;_ {τ = τ} M N) =
       μᵀ
    ∘ᵗ Tᶠ ⟦ N ⟧ᶜᵗ
    ∘ᵗ strᵀ {A = ⟦ Γ ⟧ᵉ} {τ' = τ} 
    ∘ᵗ ⟨ η-⊣ {A = ⟦ Γ ⟧ᵉ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ

  ⟦ V · W ⟧ᶜᵗ = appᵗ ∘ᵗ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵗ
  
  ⟦ absurd V ⟧ᶜᵗ = initialᵗ ∘ᵗ ⟦ V ⟧ᵛᵗ
  
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {τ} op V M) =
    let f : ⟦ Γ ⟧ᵉ →ᵗ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
        f = [ op-time op ]ᶠ (curryᵗ ⟦ M ⟧ᶜᵗ) ∘ᵗ η-⊣ in
    let g : [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
         →ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ ⟦ A ⟧ᵛ τ)
        g = [ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵍ-⟦⟧ᵛ (arity op)) (idᵗ {A = Tᵒ ⟦ A ⟧ᵛ τ})) in
    opᵀ op ∘ᵗ ⟨ ⟦⟧ᵛ-⟦⟧ᵍ (param op) ∘ᵗ ⟦ V ⟧ᵛᵗ ,
                g ∘ᵗ f ⟩ᵗ

  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {τ} {τ'} M H N) =
    let f : ⟦ Γ ⟧ᵉ →ᵗ Π Op (λ op → Π Time (λ τ'' → ⟦ Γ ⟧ᵉ))
        f = ⟨ (λ op → ⟨ (λ τ'' → idᵗ) ⟩ᵢᵗ) ⟩ᵢᵗ in
    let g : (op : Op) → (τ'' : Time)
          → ⟦ type-of-gtype (param op) ⟧ᵛ ×ᵗ [ op-time op ]ᵒ (⟦ type-of-gtype (arity op) ⟧ᵛ
              ⇒ᵗ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵗ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
          →ᵗ ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ
              ⇒ᵗ (Tᵒ ⟦ B ⟧ᵛ τ'')) ⇒ᵗ Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')
        g = λ op τ'' →
               map⇒ᵗ
                 (mapˣᵗ
                   (⟦⟧ᵍ-⟦⟧ᵛ (param op))
                   ([ op-time op ]ᶠ (map⇒ᵗ (⟦⟧ᵛ-⟦⟧ᵍ (arity op)) (idᵗ {A = Tᵒ ⟦ B ⟧ᵛ τ''}))))
                 (idᵗ {A = Tᵒ ⟦ B ⟧ᵛ (op-time op + τ'')}) in
       uncurryᵗ (
            alg-of-handler
         ∘ᵗ mapⁱˣᵗ (λ op → mapⁱˣᵗ (λ τ'' →
              g op τ'' ∘ᵗ curryᵗ (⟦ H op τ'' ⟧ᶜᵗ ∘ᵗ ×-assocᵗ)))
         ∘ᵗ f)
    ∘ᵗ mapˣᵗ idᵗ (Tᶠ ⟦ N ⟧ᶜᵗ)
    ∘ᵗ mapˣᵗ idᵗ (strᵀ {A = ⟦ Γ ⟧ᵉ} {τ' = τ})
    ∘ᵗ ⟨ idᵗ , ⟨ η-⊣ {A = ⟦ Γ ⟧ᵉ} {τ = τ} , ⟦ M ⟧ᶜᵗ ⟩ᵗ ⟩ᵗ
    
  ⟦ unbox {Γ'} {τ = τ} p q V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵗ ⟨ idᵗ ,
                    ε-⊣
                 ∘ᵗ (⟨ τ ⟩ᶠ ⟦ V ⟧ᵛᵗ)
                 ∘ᵗ ⟨⟩-≤ {A = ⟦ Γ' ⟧ᵉ} q
                 ∘ᵗ split-env-⟨⟩ p ⟩ᵗ

  ⟦ delay τs refl M ⟧ᶜᵗ =
       T-≤τ (≤-reflexive (+-comm (tctx-time τs) _))
    ∘ᵗ T-[]-tctx-module {τs = τs}
    ∘ᵗ [ τs ]ᵗᶠ ⟦ M ⟧ᶜᵗ
    ∘ᵗ [ τs ]ᵗᶠ (⟨⟩-tctx-++ᶜ τs)
    ∘ᵗ η-⊣-tctx {τs = τs}
    
  infix 25 ⟦_⟧ᶜᵗ
