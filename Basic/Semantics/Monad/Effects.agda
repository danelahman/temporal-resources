---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

-- Note: A version of the monad that is not quotioned by
--       the delay equations (identity and composition)

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Monad.Core

open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad.Effects where

-- The free graded monad generated by the operations in Op (continued)
----------------------------------------------------------------------

-- Delay operation (T is a kind of a [_]-module)

delayᵀ : ∀ {A} (τ : Time) {τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')
delayᵀ τ =
  tset-map
    (delay τ)
    (λ p c → refl)


-- Algebraic operations

opᵀ : ∀ {A τ} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ) →ᵗ Tᵒ A (op-time op + τ)
opᵀ {A} {τ} op =
  tset-map
    (λ {t} vk →
      node op
        (proj₁ (unpack-×ᵗ vk))
        (λ p y →
          map-carrier
            (unpack-⇒ᵗ (proj₂ (unpack-×ᵗ vk)))
            (pack-×ᵗ (pack-homᵒ (t + op-time op) p , y)))
        (λ p q y →
          trans
            (cong (map-carrier (unpack-⇒ᵗ (proj₂ (unpack-×ᵗ vk))))
              (trans
                (cong pack-×ᵗ
                  (cong (_, monotone ⟦ arity op ⟧ᵍ p y)
                    (sym (pack-homᵒ-monotone _ _))))
                (sym (pack-×ᵗ-monotone _ _))))
            (map-nat (unpack-⇒ᵗ (proj₂ (unpack-×ᵗ vk))) _ _)))
    (λ {t} {t'} p k →
      dcong₃ (node op)
        (sym (cong proj₁ (unpack-×ᵗ-monotone _ k)))
        (ifun-ext (fun-ext (λ q → fun-ext (λ y →
          trans
            (cong (λ (k : {t' : Time} → _ + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A _ t') → k q y)
              (subst-const _ (sym (cong proj₁ (unpack-×ᵗ-monotone p k))) _))
            (trans
              (cong (λ (f : homᵒ (t' + op-time op) ×ᵗ ⟦ arity op ⟧ᵍ →ᵗ Tᵒ A τ) → map-carrier f (pack-×ᵗ (pack-homᵒ (t' + op-time op) q , y)))
                {(unpack-⇒ᵗ (proj₂ (unpack-×ᵗ (monotone (⟦ param op ⟧ᵍ ×ᵗ [ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ)) p k))))}
                {(unpack-⇒ᵗ (monotone (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ) (+-mono-≤ p ≤-refl) (proj₂ (unpack-×ᵗ k))))}
                (cong unpack-⇒ᵗ (sym (cong proj₂ (unpack-×ᵗ-monotone _ _)))))
              (unpack-⇒ᵗ-map-carrier (proj₂ (unpack-×ᵗ k)) _ _ y))))))
        (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip)))))))

