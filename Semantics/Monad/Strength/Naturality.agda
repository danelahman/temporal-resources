---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

module Semantics.Monad.Strength.Naturality where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.TSets
open import Semantics.Modality.Future
open import Semantics.Modality.Past
open import Semantics.Monad.Core
open import Semantics.Monad.Strength

open import Util.Equality
open import Util.Operations
open import Util.Time

-- The strength of the monad generated by the operations in Op (continued)
-------------------------------------------------------------------------
            
-- Naturality

strˢ-nat : ∀ {A A' B B' τ t}
         → (f : A →ᵗ A')
         → (g : B →ᵗ B')
         → (v : carrier ([ τ ]ᵒ A) t)
         → (c : Tˢ B τ t)
         → map-carrier (strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g)) (pack-×ᵗ (v , c))
         ≡ map-carrier (Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ {A} {B}) (pack-×ᵗ (v , c))
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (leaf w) =
  trans
    (∘ᵗ-reveal _ _ _)
    (trans
      (trans
        (cong (map-carrier strᵀ)
          (⟨⟩ᵗ-reveal _ _ _))
        (trans
          (trans
            (cong (map-carrier strᵀ)
              (cong pack-×ᵗ
                (cong₂ _,_
                  (trans
                    (∘ᵗ-reveal _ _ _)
                    (trans
                      ([]-reveal _ _ _)
                      (cong (map-carrier f)
                        (trans
                          (fstᵗ-reveal _)
                          (cong proj₁ (pack-unpack-×ᵗ _))))))
                  (trans
                    (∘ᵗ-reveal _ _ _)
                    (cong (map-carrier (Tᶠ g))
                      (trans
                        (sndᵗ-reveal _)
                        (cong proj₂ (pack-unpack-×ᵗ _))))))))
            (trans
              (cong₂ strˢ
                (cong proj₁ (pack-unpack-×ᵗ _))
                (cong proj₂ (pack-unpack-×ᵗ _)))
              (cong leaf
                (trans
                  (cong pack-×ᵗ
                    (cong₂ _,_
                      (trans
                        (sym (map-nat f _ _))
                        (sym
                          (trans
                            (∘ᵗ-reveal _ _ _)
                            (cong (map-carrier f)
                              (trans
                                (fstᵗ-reveal _)
                                (cong proj₁ (pack-unpack-×ᵗ _)))))))
                      (sym
                        (trans
                          (∘ᵗ-reveal _ _ _)
                          (cong (map-carrier g)
                            (trans
                              (sndᵗ-reveal _)
                              (cong proj₂ (pack-unpack-×ᵗ _))))))))
                  (sym (⟨⟩ᵗ-reveal _ _ _))))))
          (cong (map-carrier (Tᶠ (mapˣᵗ f g)))
            (sym
              (cong₂ strˢ
                (cong proj₁ (pack-unpack-×ᵗ _))
                (cong proj₂ (pack-unpack-×ᵗ _)))))))
      (sym (∘ᵗ-reveal _ _ _)))
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (op-node op w k k-nat) =
  trans
    (∘ᵗ-reveal _ _ _)
    (trans
      (trans
        (cong (map-carrier strᵀ)
          (trans
            (⟨⟩ᵗ-reveal _ _ _)
            (cong pack-×ᵗ
              (cong₂ _,_
                (trans
                  (∘ᵗ-reveal _ _ _)
                  (trans
                    ([]-reveal _ _ _)
                    (cong (map-carrier f)
                      (trans
                        (fstᵗ-reveal _)
                        (cong proj₁ (pack-unpack-×ᵗ _))))))
                (trans
                  (∘ᵗ-reveal _ _ _)
                  (cong (map-carrier (Tᶠ g))
                    (trans
                      (sndᵗ-reveal _)
                      (cong proj₂ (pack-unpack-×ᵗ _)))))))))
        (trans
          (cong₂ strˢ
            (cong proj₁ (pack-unpack-×ᵗ _))
            (cong proj₂ (pack-unpack-×ᵗ _)))
          (trans
            (dcong₂ (op-node op w)
              (ifun-ext (fun-ext (λ p → fun-ext (λ y →
                trans
                  (trans
                    (trans
                      (cong₂ strˢ
                        (sym
                          (trans
                            (cong (λ xy → proj₁ (unpack-×ᵗ xy))
                              (⟨⟩ᵗ-reveal _ _ _))
                            (trans
                              (cong proj₁ (pack-unpack-×ᵗ _))
                              (trans
                                (∘ᵗ-reveal _ _ _)
                                (trans
                                  ([]-reveal _ _ _)
                                  (trans
                                    (cong (map-carrier f)
                                      (trans
                                        (fstᵗ-reveal _)
                                        (cong proj₁ (pack-unpack-×ᵗ _))))
                                    (map-nat f _ v)))))))
                        (sym
                          (trans
                            (cong (λ xy → proj₂ (unpack-×ᵗ xy))
                              (⟨⟩ᵗ-reveal _ _ _))
                            (trans
                              (cong proj₂ (pack-unpack-×ᵗ _))
                              (trans
                                (∘ᵗ-reveal _ _ _)
                                (cong (Tˢᶠ g)
                                  (trans
                                    (sndᵗ-reveal _)
                                    (cong proj₂ (pack-unpack-×ᵗ _)))))))))
                      (sym (∘ᵗ-reveal _ _ _)))
                    (strˢ-nat f g
                      (monotone A
                        (≤-trans
                          (≤-reflexive (sym (+-assoc t (op-time op) _)))
                          (+-monoˡ-≤ _ p)) v)
                      (k p y) ))
                  (trans
                    (∘ᵗ-reveal _ _ _)
                    (cong (Tˢᶠ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ)
                      (cong₂ strˢ
                        (cong proj₁ (pack-unpack-×ᵗ _))
                        (cong proj₂ (pack-unpack-×ᵗ _)))))))))
              (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip)))))))
            (cong (Tˢᶠ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ)
              (sym
                (cong₂ strˢ
                  (cong proj₁ (pack-unpack-×ᵗ _))
                  (cong proj₂ (pack-unpack-×ᵗ _))))))))
      (sym (∘ᵗ-reveal _ _ _)))
strˢ-nat {A} {A'} {B} {B'} {_} {t} f g v (delay-node τ k) =
  trans
    (∘ᵗ-reveal _ _ _)
    (trans
      (trans
        (cong (map-carrier strᵀ)
          (trans
            (⟨⟩ᵗ-reveal _ _ _)
            (cong pack-×ᵗ
              (cong₂ _,_
                (trans
                  (∘ᵗ-reveal _ _ _)
                  (trans
                    ([]-reveal _ _ _)
                    (cong (map-carrier f)
                      (trans
                        (fstᵗ-reveal _)
                        (cong proj₁ (pack-unpack-×ᵗ _))))))
                (trans
                  (∘ᵗ-reveal _ _ _)
                  (cong (map-carrier (Tᶠ g))
                    (trans
                        (sndᵗ-reveal _)
                        (cong proj₂ (pack-unpack-×ᵗ _)))))))))
        (trans
          (cong₂ strˢ
            (cong proj₁ (pack-unpack-×ᵗ _))
            (cong proj₂ (pack-unpack-×ᵗ _)))
          (trans
            (cong (delay-node τ)
              (trans
                (sym
                  (trans
                    (∘ᵗ-reveal _ _ _)
                    (trans
                      (cong (map-carrier strᵀ)
                        (⟨⟩ᵗ-reveal _ _ _))
                      (cong₂ strˢ
                        (trans
                          (cong proj₁ (pack-unpack-×ᵗ _))
                          (trans
                            (∘ᵗ-reveal _ _ _)
                            (trans
                              ([]-reveal _ _ _)
                              (trans
                                (cong (map-carrier f)
                                  (trans
                                    (fstᵗ-reveal _)
                                    (cong proj₁ (pack-unpack-×ᵗ _))))
                                (map-nat f _ v)))))
                        (trans
                          (cong proj₂ (pack-unpack-×ᵗ _))
                          (trans
                            (∘ᵗ-reveal _ _ _)
                            (cong (Tˢᶠ g)
                              (trans
                                (sndᵗ-reveal _)
                                (cong proj₂ (pack-unpack-×ᵗ _))))))))))
                (trans
                  (strˢ-nat f g (monotone A (≤-reflexive (sym (+-assoc t _ _))) v) k)
                  (trans
                    (∘ᵗ-reveal _ _ _)
                    (cong (Tˢᶠ ⟨ f ∘ᵗ fstᵗ , g ∘ᵗ sndᵗ ⟩ᵗ)
                      (cong₂ strˢ
                        (cong proj₁ (pack-unpack-×ᵗ _))
                        (cong proj₂ (pack-unpack-×ᵗ _))))))))
            (sym
              (cong (map-carrier (Tᶠ (mapˣᵗ f g)))
                (cong₂ strˢ
                  (cong proj₁ (pack-unpack-×ᵗ _))
                  (cong proj₂ (pack-unpack-×ᵗ _)) ))))))
      (sym (∘ᵗ-reveal _ _ _)))


strᵀ-nat : ∀ {A A' B B' τ}
          → (f : A →ᵗ A')
          → (g : B →ᵗ B')
          →  strᵀ {A'} {B'} ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g)
          ≡ᵗ Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ {A} {B}
strᵀ-nat {A} {A'} {B} {B'} {τ} f g =
  eqᵗ (λ vc →
    trans
      (cong (map-carrier (strᵀ ∘ᵗ mapˣᵗ ([ τ ]ᶠ f) (Tᶠ g))) (sym (unpack-pack-×ᵗ vc)))
      (trans
        (strˢ-nat f g (proj₁ (unpack-×ᵗ vc)) (proj₂ (unpack-×ᵗ vc)))
        (cong (map-carrier (Tᶠ (mapˣᵗ f g) ∘ᵗ strᵀ)) (unpack-pack-×ᵗ vc))))

