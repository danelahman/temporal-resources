---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Monad.Core
open import Semantics.Monad.Effects

open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad.Effects.Algebraicity where

-- The (algebraic) operations of the monad generated by the operations in Op (continued)
----------------------------------------------------------------------------------------

-- Algebraicity of the delay operation

delayᵀ-algebraicity : ∀ {A} (τ : Time) {τ' τ''}
                    →     μᵀ {A} {τ + τ'} {τ''}
                       ∘ᵗ delayᵀ τ {τ'}
                    ≡ᵗ    τ-substᵀ (sym (+-assoc τ τ' τ''))
                       ∘ᵗ delayᵀ τ
                       ∘ᵗ [ τ ]ᶠ (μᵀ {A} {τ'} {τ''})
delayᵀ-algebraicity {A} τ {τ'} {τ''} =
  eqᵗ (λ {t} c →
    trans
      (∘ᵗ-reveal _ _ _)
      (trans
        (trans
          (cong (τ-subst (sym (+-assoc τ τ' τ'')))
            (cong (delay τ) (sym ([]-reveal _ _ _))))
          (cong (map-carrier (τ-substᵀ (sym (+-assoc τ τ' τ''))))
            (sym (∘ᵗ-reveal _ _ _))))
        (sym (∘ᵗ-reveal _ _ _))))


-- Algebraicity of the (other) algebraic operations

opᵀ-algebraicity : ∀ {A τ τ'} → (op : Op)
                 →     μᵀ {A} {op-time op + τ} {τ'}
                    ∘ᵗ opᵀ {τ = τ} op
                 ≡ᵗ    τ-substᵀ (sym (+-assoc (op-time op) τ τ'))
                    ∘ᵗ opᵀ op
                    ∘ᵗ mapˣᵗ idᵗ ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ))
opᵀ-algebraicity {A} {τ} {τ'} op =
  eqᵗ (λ {t} c →
    trans
      (∘ᵗ-reveal _ _ _)
      (trans
        (trans
          (cong (τ-subst (sym (+-assoc (op-time op) τ τ')))
            (dcong₃ (node op)
              (sym
                (trans
                  (cong (λ xy → proj₁ (unpack-×ᵗ xy)) (⟨⟩ᵗ-reveal _ _ _))
                  (trans
                    (cong proj₁ (pack-unpack-×ᵗ _))
                    (trans
                      (∘ᵗ-reveal _ _ _)
                      (trans
                        (idᵗ-reveal _)
                        (fstᵗ-reveal _))))))
              (trans
                (subst-const
                  ({t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A (τ + τ') t')
                  (sym
                    (trans
                      (cong (λ xy → proj₁ (unpack-×ᵗ xy))
                        (⟨⟩ᵗ-reveal
                         (tset-map (map-carrier (idᵗ ∘ᵗ fstᵗ)) (map-nat (idᵗ ∘ᵗ fstᵗ)))
                         ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ) ∘ᵗ sndᵗ) c))
                      (trans
                        (cong proj₁
                          (pack-unpack-×ᵗ
                           (map-carrier (idᵗ ∘ᵗ fstᵗ) c ,
                            map-carrier ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ) ∘ᵗ sndᵗ) c)))
                        (trans
                          (∘ᵗ-reveal (tset-map (map-carrier idᵗ) (map-nat idᵗ)) fstᵗ c)
                          (trans (idᵗ-reveal (map-carrier fstᵗ c)) (fstᵗ-reveal c))))))
                  _)
                (ifun-ext (fun-ext (λ p → fun-ext (λ y →
                  sym
                    (trans
                      (cong
                        (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                        (cong
                          (λ xy → unpack-⇒ᵗ (proj₂ (unpack-×ᵗ {⟦ param op ⟧ᵍ} {[ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A (τ + τ'))} xy)))
                          (⟨⟩ᵗ-reveal _ _ _)))
                      (trans
                        (cong
                          (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                          (cong
                            (λ xy → unpack-⇒ᵗ (proj₂ xy))
                            (pack-unpack-×ᵗ {⟦ param op ⟧ᵍ} {[ op-time op ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A (τ + τ'))} _)))
                        (trans
                          (cong
                            (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                            (cong unpack-⇒ᵗ (∘ᵗ-reveal ([ op-time op ]ᶠ (map⇒ᵗ idᵗ μᵀ)) sndᵗ c)))
                          (trans
                            (cong
                              (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                              (cong unpack-⇒ᵗ ([]-reveal (op-time op) (map⇒ᵗ idᵗ μᵀ) (map-carrier sndᵗ c))))
                            (trans
                              (cong
                                (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                                (cong unpack-⇒ᵗ (map⇒ᵗ-reveal idᵗ μᵀ (map-carrier sndᵗ c))))
                              (trans
                                (cong
                                  (λ f → map-carrier f (pack-×ᵗ {homᵒ (t + op-time op)} {⟦ arity op ⟧ᵍ} (pack-homᵒ (t + op-time op) p , y)))
                                  (pack-unpack-⇒ᵗ (μᵀ ∘ᵗ unpack-⇒ᵗ (map-carrier sndᵗ c) ∘ᵗ mapˣᵗ idᵗ idᵗ)))
                                (trans
                                  (∘ᵗ-reveal _ _ _)
                                  (cong
                                    (μˢ {A})
                                    {map-carrier
                                      (unpack-⇒ᵗ (map-carrier sndᵗ c) ∘ᵗ ⟨ idᵗ ∘ᵗ fstᵗ , idᵗ ∘ᵗ sndᵗ ⟩ᵗ)
                                      (pack-×ᵗ (pack-homᵒ (t + op-time op) p , y))}
                                    {map-carrier
                                      (unpack-⇒ᵗ (proj₂ (unpack-×ᵗ c)))
                                      (pack-×ᵗ (pack-homᵒ (t + op-time op) p , y))}
                                    (trans
                                      (∘ᵗ-reveal _ _ _)
                                      (trans
                                        (cong
                                          (λ f → map-carrier f (map-carrier ⟨ idᵗ ∘ᵗ fstᵗ , idᵗ ∘ᵗ sndᵗ ⟩ᵗ (pack-×ᵗ (pack-homᵒ (t + op-time op) p , y))))
                                          (cong unpack-⇒ᵗ (sndᵗ-reveal c)))
                                        (cong (map-carrier (unpack-⇒ᵗ (proj₂ (unpack-×ᵗ c))))
                                          (trans
                                            (⟨⟩ᵗ-reveal _ _ _)
                                            (cong pack-×ᵗ
                                              (cong₂ _,_
                                                (trans
                                                  (∘ᵗ-reveal _ _ _)
                                                  (trans
                                                    (idᵗ-reveal _)
                                                    (trans
                                                      (fstᵗ-reveal _)
                                                      (cong proj₁ (pack-unpack-×ᵗ _)))))
                                                (trans
                                                  (∘ᵗ-reveal _ _ _)
                                                  (trans
                                                    (idᵗ-reveal _)
                                                    (trans
                                                      (sndᵗ-reveal _)
                                                      (cong proj₂ (pack-unpack-×ᵗ _))))))))))))))))))))))))
              (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
          (cong (map-carrier (τ-substᵀ (sym (+-assoc (op-time op) τ τ'))))
            (sym (∘ᵗ-reveal _ _ _))))
        (sym (∘ᵗ-reveal _ _ _))))
