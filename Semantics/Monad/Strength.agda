---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

module Semantics.Monad.Strength where

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

-- The strength of the monad generated by the operations in Op
--------------------------------------------------------------

mutual

  {-# TERMINATING #-}

  strˢ : ∀ {A B τ t}
       → carrier ([ τ ]ᵒ A) t
       → Tˢ B τ t
       → Tˢ (A ×ᵗ B) τ t
  strˢ {A} {B} v (leaf w) =
    leaf
      (pack-×ᵗ
        (monotone A (≤-reflexive (+-identityʳ _)) v ,
         w))
  strˢ {A} {B} {_} {t} v (op-node {τ = τ} op w k k-nat) =
    op-node op w
      (λ p y →
        strˢ {A} {B}
          (monotone A
            (≤-trans
              (≤-reflexive (sym (+-assoc t (op-time op) τ)))
              (+-monoˡ-≤ τ p)) v)
          (k p y))
      (λ p q y →
        trans
          (cong₂ strˢ
            (trans
              (cong (λ p →  monotone A p v) (≤-irrelevant _ _))
              (sym
                (monotone-trans A _ _ _)))
            (k-nat p q y))
          (strˢ-≤t-nat p _ (k q y)))
  strˢ {A} {B} {_} {t} v (delay-node τ k) =
    delay-node τ
      (strˢ {A} {B}
        (monotone A (≤-reflexive (sym (+-assoc t τ _))) v)
        k)

  strˢ-≤t-nat : ∀ {A B τ} → {t t' : ℕ} → (p : t ≤ t')
              → (v : carrier ([ τ ]ᵒ A) t)
              → (c : Tˢ B τ t)
              → strˢ {A = A} {B = B}
                  (monotone ([ τ ]ᵒ A) p v)
                  (Tˢ-≤t p c)
              ≡ Tˢ-≤t p (strˢ {A = A} {B = B} v c)
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (leaf w) =
    cong leaf
      (trans
        (cong pack-×ᵗ
          (cong (_, monotone B p w)
            (trans
              (monotone-trans A _ _ v)
              (trans
                (cong (λ p → monotone A p v) (≤-irrelevant _ _))
                (sym (monotone-trans A _ _ v))))))
        (sym (pack-×ᵗ-monotone p _)))
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (op-node op w k k-nat) =
    dcong₂ (op-node op (monotone ⟦ param op ⟧ᵍ p w))
      (ifun-ext (fun-ext (λ q → fun-ext (λ y →
        cong (λ x → strˢ x (k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y))
          (trans
            (monotone-trans A _ _ v)
            (cong (λ p → monotone A p v) (≤-irrelevant _ _)))))))
      (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))
  strˢ-≤t-nat {A} {B} {_} {t} {t'} p v (delay-node τ k) =
    cong (delay-node τ)
      (trans
        (cong (λ x → strˢ x (Tˢ-≤t (+-monoˡ-≤ τ p) k))
          (trans
            (monotone-trans A _ _ v)
            (trans
              (cong (λ p → monotone A p v) (≤-irrelevant _ _))
              (sym (monotone-trans A _ _ v)))))
        (strˢ-≤t-nat _ _ k))

strᵀ : ∀ {A B τ}
     → [ τ ]ᵒ A ×ᵗ Tᵒ B τ →ᵗ Tᵒ (A ×ᵗ B) τ
strᵀ {A} {B} {τ} =
  tset-map
    (λ vc → strˢ {A} {B} (proj₁ (unpack-×ᵗ vc)) (proj₂ (unpack-×ᵗ vc)))
    (λ p vc →
      trans
        (cong₂ strˢ
          (sym (cong proj₁ (unpack-×ᵗ-monotone {[ τ ]ᵒ A} {Tᵒ B τ} p vc)))
          (sym (cong proj₂ (unpack-×ᵗ-monotone {[ τ ]ᵒ A} {Tᵒ B τ} p vc))))
        (strˢ-≤t-nat p _ _))

