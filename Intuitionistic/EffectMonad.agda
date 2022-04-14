---------------------------------------------------------------
-- Free graded monad generated by algebraic operations in Op --
---------------------------------------------------------------

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language

open import TSets
open import ContextModality
open import TypeModality
open import ModalityAdjunction

module EffectMonad where

-- Base types are interpreted as constant presheaves

BaseTSet : BaseType → TSet
BaseTSet B = tset (λ _ → BaseSet B) (λ _ → id) (λ _ → refl) (λ _ _ _ → refl)

constᵗ : ∀ {B} → BaseSet B → 𝟙ᵗ →ᵗ BaseTSet B
constᵗ c = tset-map (λ _ → c)

-- Interpretation of ground types

⟦_⟧ᵍ : GType → TSet
⟦ Base B ⟧ᵍ = BaseTSet B
⟦ Unit ⟧ᵍ   = 𝟙ᵗ
⟦ Empty ⟧ᵍ  = 𝟘ᵗ

⟦⟧ᵍ-constant : (B : GType) → (t t' : Time) → carrier ⟦ B ⟧ᵍ t → carrier ⟦ B ⟧ᵍ t'
⟦⟧ᵍ-constant (Base B) t t' = id
⟦⟧ᵍ-constant Unit     t t' = id
⟦⟧ᵍ-constant Empty    t t' = id

-- Object-mapping of the underlying functor

data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where  -- 1st time index (τ) is the duration of the computation (its time-grading)
                                                          -- 2nd time index (t) is the corresponding TSets' time-index (modal time)
  leaf : ∀ {τ t}
       → carrier A (τ + t)
       → Tˢ A τ t

  node : ∀ {τ τ' t}
       → (op : Op)
       → carrier ⟦ param op ⟧ᵍ t
       → ({t' : Time} → t + op-time op ≤ t' → carrier (⟦ arity op ⟧ᵍ) t' → Tˢ A τ t')  -- intuitively, [ op-time op ] (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ)
       → τ' ≡ op-time op + τ                                                           -- abstracting into a variable for easier recursive defs.
       → Tˢ A τ' t

-- Monotonicity wrt TSets' time-indices

Tˢ-≤t : ∀ {A τ t t'} → t ≤ t' → Tˢ A τ t → Tˢ A τ t'
Tˢ-≤t {A} p (leaf a) =
  leaf (monotone A (+-monoʳ-≤ _ p) a)
Tˢ-≤t {A} p (node op v k q) =
  node
    op (monotone ⟦ param op ⟧ᵍ p v)
    (λ q y → Tˢ-≤t ≤-refl (k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y)) q

Tˢ-≤t-refl : ∀ {A τ t} → (c : Tˢ A τ t) → Tˢ-≤t ≤-refl c ≡ c
Tˢ-≤t-refl {A} (leaf v) =
  cong
    leaf
    (trans
      (cong (λ p → monotone A p v) (≤-irrelevant _ ≤-refl))
      (monotone-refl A v))
Tˢ-≤t-refl {A} (node {τ} {τ'} {t} op v k p) =
  trans
    (cong
      (λ v → node op v _ p)
      (monotone-refl ⟦ param op ⟧ᵍ v))
    (cong
      (λ (k : ({t' : Time} → t + op-time op ≤ t'
                           → carrier (⟦ arity op ⟧ᵍ) t' → Tˢ A τ t')) → node op v k p)
      (ifun-ext (fun-ext (λ q → fun-ext (λ y →
        trans
          (cong (λ q → Tˢ-≤t ≤-refl (k q y)) (≤-irrelevant _ _))
          (Tˢ-≤t-refl (k q y)))))))

Tˢ-≤t-trans : ∀ {A τ t t' t''} → (p : t ≤ t') → (q : t' ≤ t'')
            → (c : Tˢ A τ t) → Tˢ-≤t q (Tˢ-≤t p c) ≡ Tˢ-≤t (≤-trans p q) c

Tˢ-≤t-trans {A} p q (leaf v) =
  cong
    leaf
    (trans
      (monotone-trans A _ _ v)
      (cong (λ p → monotone A p v) (≤-irrelevant _ _)))
Tˢ-≤t-trans {A} p q (node op v k r) =
  trans
    (cong
      (λ v → node op v _ r)
      (monotone-trans ⟦ param op ⟧ᵍ p q v))
    (cong (λ (k : ({t' : Time} → _ + op-time op ≤ t'
                               → carrier (⟦ arity op ⟧ᵍ) t' → Tˢ A _ t'))
                               → node op (monotone ⟦ param op ⟧ᵍ (≤-trans p q) v) k r)
       (ifun-ext (fun-ext (λ s → fun-ext (λ c →
         trans
           (Tˢ-≤t-trans (≤-reflexive refl) (≤-reflexive refl) _)
           (cong₂ Tˢ-≤t
             (≤-irrelevant _ _)
             (cong (λ p → k p c) (≤-irrelevant _ _))))))))

-- Monotonicity wrt time-gradings

Tˢ-≤τ : ∀ {A τ τ' t} → τ ≤ τ' → Tˢ A τ t → Tˢ A τ' t
Tˢ-≤τ {A} p (leaf v) = leaf (monotone A (+-monoˡ-≤ _ p) v)
Tˢ-≤τ p (node op v k q) =
  node
    op v
    (λ r y → Tˢ-≤τ (proj₂ (proj₂ (n≡m+k≤n' (trans q (+-comm (op-time op) _)) p))) (k r y))
    (trans (proj₁ (proj₂ (n≡m+k≤n' (trans q (+-comm (op-time op) _)) p))) (+-comm _ (op-time op)))

-- Functorial action on →ᵗ

Tˢᶠ : ∀ {A B τ} → A →ᵗ B → {t : Time} → Tˢ A τ t → Tˢ B τ t
Tˢᶠ (tset-map f) (leaf a)   =
  leaf (f a)
Tˢᶠ (tset-map f) (node op v k q) =
  node op v (λ p y → Tˢᶠ (tset-map f) (k p y)) q

-- Packaging it all up into a functor

Tᵒ : TSet → Time → TSet
Tᵒ A τ = tset (λ t → Tˢ A τ t) Tˢ-≤t Tˢ-≤t-refl Tˢ-≤t-trans

Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ
Tᶠ f = tset-map (Tˢᶠ f)

T-≤τ : ∀ {A τ τ'} → τ ≤ τ' → Tᵒ A τ →ᵗ Tᵒ A τ'
T-≤τ p = tset-map (Tˢ-≤τ p)

-- Unit

ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0
ηᵀ = tset-map (λ v → leaf v)

-- T is a [_]-module

T-[]-moduleˢ : ∀ {A τ τ' t} → Tˢ A τ' (t + τ) → Tˢ A (τ + τ') t
T-[]-moduleˢ {A} {τ} {τ'} {t} (leaf v) =
  leaf (monotone A (≤-reflexive (trans
                          (trans
                            (cong (τ' +_) (+-comm t τ))
                            (sym (+-assoc τ' τ t)))
                          (cong (_+ t) (+-comm τ' τ)))) v)
T-[]-moduleˢ {A} {τ} {τ'} {t} (node {τ = τ''} op v k p) =
  node op
    (⟦⟧ᵍ-constant (param op) (t + τ) t v)    -- can't use monotonicity of the parameter type
    (λ {t'} q y → T-[]-moduleˢ (k (≤-trans
                                    (≤-reflexive
                                      (trans
                                        (+-assoc t τ (op-time op))
                                        (trans
                                          (cong (t +_) (+-comm τ (op-time op)))
                                          (sym (+-assoc t (op-time op) τ)))))
                                    (+-monoˡ-≤ τ q))
                                  (monotone ⟦ arity op ⟧ᵍ (m≤m+n t' τ) y)))  -- could also have used ⟦⟧ᵍ-constant
    (trans
      (cong (τ +_) p)
      (trans
        (sym (+-assoc τ (op-time op) τ''))
        (trans
          (cong (_+ τ'') (+-comm τ (op-time op)))
          (+-assoc (op-time op) τ _))))

T-[]-module : ∀ {A τ τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')
T-[]-module = tset-map T-[]-moduleˢ

-- Kleisli extension

kl-extˢ : ∀ {A B τ τ'} → {t : Time}
        → carrier (Tᵒ A τ) t
        → carrier ([ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')) t
        → carrier (Tᵒ B (τ + τ')) t
        
kl-extˢ {A} {B} {τ' = τ'} (leaf {τ} {t} v) f =
  T-[]-moduleˢ
    (monotone
      (Tᵒ B τ')
      (≤-reflexive (+-comm τ t))
      (f (≤-reflexive (+-comm t τ)) v))
kl-extˢ {A = A} {B = B} {τ' = τ'} {t} (node {τ = τ} op v k p) f =
  node op v
    (λ {t'} q y →
      kl-extˢ
        (k q y)
        (λ {t''} r x →
          f (≤-trans
              (≤-trans
                (≤-reflexive (cong (t +_) p))
                (≤-trans
                  (≤-reflexive (sym (+-assoc t (op-time op) τ)))
                  (+-monoˡ-≤ τ q))) r)
            x))
    (trans (cong (_+ τ') p) (+-assoc (op-time op) τ τ'))

kl-extᵀ : ∀ {A B τ τ'} → Tᵒ A τ ×ᵗ [ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ') →ᵗ Tᵒ B (τ + τ')
kl-extᵀ = tset-map (λ (c , f) → kl-extˢ c f)

-- Algebraic operations

opᵀ : ∀ {A τ} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ)) →ᵗ Tᵒ A (op-time op + τ)
opᵀ op = tset-map (λ { (v , k) → node op v k refl })
