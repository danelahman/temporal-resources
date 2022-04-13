---------------------------------------
-- Equational theory of the language --
---------------------------------------

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

open import Language
open import ContextModality
open import Renamings
open import Substitutions

module EquationalTheory where

-- Equations between well-typed values and computations

mutual

  -- value equations

  data _⊢V⦂_==_ (Γ : Ctx) : {A : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    -- reflexivity, symmetry, transitivity
  
    ⊢V⦂-refl : ∀ {A}
            → (V : Γ ⊢V⦂ A)
            --------------
            → Γ ⊢V⦂ V == V

    ⊢V⦂-sym : ∀ {A}
           → {V W : Γ ⊢V⦂ A}
           → Γ ⊢V⦂ V == W
           ----------------
           → Γ ⊢V⦂ W == V

    ⊢V⦂-trans : ∀ {A}
             → {V W U : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == W
             → Γ ⊢V⦂ W == U
             -------------------
             → Γ ⊢V⦂ V == U

    -- congruence equations

    lam-cong : ∀ {A B τ}
             → {M N : Γ ∷ A ⊢C⦂ B ‼ τ}
             → Γ ∷ A ⊢C⦂ M == N
             -------------------------
             → Γ ⊢V⦂ lam M == lam N

    box-cong : ∀ {A τ}
             → {V W : Γ ⟨ τ ⟩ ⊢V⦂ A}
             → Γ ⟨ τ ⟩ ⊢V⦂ V == W
             -----------------------
             → Γ ⊢V⦂ box V == box W

    -- eta equations

    ⋆-eta : (V : Γ ⊢V⦂ Unit)
          -----------------
          → Γ ⊢V⦂ V == ⋆

    lam-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            --------------------------------------------
            → Γ ⊢V⦂ V == lam (V-rename wk-ren V · var Hd)

  infix 18 _⊢V⦂_==_

  -- computation equations

  data _⊢C⦂_==_ (Γ : Ctx) : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- reflexivity, symmetry, transitivity
  
    ⊢C⦂-refl : ∀ {C}
            → (M : Γ ⊢C⦂ C)
            --------------
            → Γ ⊢C⦂ M == M

    ⊢C⦂-sym : ∀ {C}
           → {M N : Γ ⊢C⦂ C}
           → Γ ⊢C⦂ M == N
           ----------------
           → Γ ⊢C⦂ N == M

    ⊢C⦂-trans : ∀ {C}
             → {M N P : Γ ⊢C⦂ C}
             → Γ ⊢C⦂ M == N
             → Γ ⊢C⦂ N == P
             -------------------
             → Γ ⊢C⦂ M == P

    -- congruence equations

    -- return-cong

    -- ;-cong

    -- app-cong

    -- absurd-cong

    -- perform-cong

    -- unbox-cong

    -- coerce-cong

    -- computational/beta equations for sequential composition

    return-; : ∀ {A B τ}
             → (V : Γ ⊢V⦂ A)
             → (M : Γ ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ)
             ----------------------------------------------------------------
             → Γ ⊢C⦂ return V ; M
                 == C-rename ⟨⟩-eta-ren (M [ Hd ↦ V-rename ⟨⟩-eta⁻¹-ren V ]c)   -- M[V/x]
                  
    perform-; : ∀ {A B τ τ'}
              → (op : Op)
              → (V : Γ ⊢V⦂ type-of-gtype (param op))
              → (M : Γ ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ)
              → (N : Γ ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
              -----------------------------------------------------------------------------------------------------
              → Γ ⊢C⦂ (perform op V M) ; N
                  == coerce (≤-reflexive (sym (+-assoc (op-time op) τ τ')))     -- perform op V (M ; N)
                       (C-rename
                         (⟨⟩-mon-ren (≤-reflexive (trans
                                                    (sym (n∸n≡0 (op-time op + τ + τ')))
                                                    (cong (op-time op + τ + τ' ∸_) (+-assoc (op-time op) τ τ'))))
                          ∘ʳ ⟨⟩-eta⁻¹-ren)
                         (perform op V
                           (M ;
                             C-rename (cong-ren {Γ'' = [] ⟨ τ ⟩ ∷ A} wk-ren ∘ʳ
                               cong-ren {Γ'' = [] ∷ A} ⟨⟩-mu-ren ) N)))

    coerce-; : ∀ {A B τ τ' τ''}
             → (p : τ ≤ τ')
             → (M : Γ ⟨ τ' ∸ τ ⟩ ⊢C⦂ A ‼ τ)
             → (N : Γ ⟨ τ' ⟩ ∷ A ⊢C⦂ B ‼ τ'')
             -------------------------------------------------------------------------------------
             → Γ ⊢C⦂ coerce p M ; N
                 == coerce                         -- coerce (p + id) (M ; N)
                      (+-monoˡ-≤ τ'' p)
                      (C-rename
                         (⟨⟩-mon-ren (≤-reflexive (trans
                                                    (sym ([m+n]∸[m+o]≡n∸o τ'' τ' τ))
                                                    (cong₂ _∸_ (+-comm τ'' τ') (+-comm τ'' τ)))))
                         M ;
                       C-rename
                         (cong-ren {Γ'' = [] ∷ A}
                           (⟨⟩-mu-ren
                            ∘ʳ ⟨⟩-mon-ren (≤-reflexive
                                            (trans
                                              (trans
                                                (sym (m∸n+n≡m p))
                                                (cong (_+ τ) (sym ([m+n]∸[m+o]≡n∸o τ'' τ' τ))))
                                              (cong₂ (λ t t' → t ∸ (t') + τ)
                                                (+-comm τ'' τ') (+-comm τ'' τ))))))
                         N)

    -- associativity equation for sequential composition

    ;-assoc : ∀ {A B C τ τ' τ''}
            → (M : Γ ⊢C⦂ A ‼ τ)
            → (N : Γ ⟨ τ ⟩ ∷ A ⊢C⦂ B ‼ τ')
            → (P : Γ ⟨ τ + τ' ⟩ ∷ B ⊢C⦂ C ‼ τ'')
            -----------------------------------------------------------------------------------
            → Γ ⊢C⦂ (M ; N) ; P
                == coerce (≤-reflexive (sym (+-assoc τ τ' τ'')))            -- M ; (N ; P)
                     (C-rename
                       (⟨⟩-mon-ren (≤-reflexive (trans
                                                 (sym (n∸n≡0 (τ + τ' + τ'')))
                                                 (cong (τ + τ' + τ'' ∸_) (+-assoc τ τ' τ''))))
                        ∘ʳ ⟨⟩-eta⁻¹-ren)
                       (M ;
                         (N ;
                           C-rename (cong-ren {Γ'' = [] ⟨ τ' ⟩ ∷ B} wk-ren ∘ʳ
                             cong-ren {Γ'' = [] ∷ B} ⟨⟩-mu-ren ) P)))


    -- computational/beta equation for function application

    app-lam : ∀ {A C}
            → (M : Γ ∷ A ⊢C⦂ C)
            → (W : Γ ⊢V⦂ A)
            ------------------------
            → Γ ⊢C⦂ lam M · W == (M [ Hd ↦ W ]c)

    -- computational/beta equation for unboxing

    unbox-box : ∀ {Γ' Γ'' A B τ τ'}
              → (p : Γ' , Γ'' split Γ)
              → (q : τ ≤ ctx-delay Γ'')
              → (V : Γ' ⟨ τ ⟩ ⊢V⦂ A)
              → (N : Γ ∷ A ⊢C⦂ B ‼ τ')
              -----------------------------------------------
              → Γ ⊢C⦂ unbox p q (box V) N
                  == (N [ Hd ↦ V-rename (wk-⟨⟩-ren p q) V ]c)

    -- eta equations

    ;-return-eta : ∀ {A τ}
                 → (M : Γ ⊢C⦂ A ‼ τ)
                 ----------------------------------------------------------------------------
                 → Γ ⊢C⦂ M
                     == coerce (≤-reflexive (+-identityʳ τ))            -- M ; return x
                          (C-rename
                             (⟨⟩-mon-ren (≤-reflexive (trans
                                                        (sym (n∸n≡0 τ))
                                                        (cong (τ ∸_) (sym (+-identityʳ τ)))))
                             ∘ʳ ⟨⟩-eta⁻¹-ren)
                             M ;
                          return (var Hd))

    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ Empty)
               → (M : Γ ⊢C⦂ C)
               ---------------------
               → Γ ⊢C⦂ absurd V == M

    box-unbox-eta : ∀ {Γ' A C τ}
                  → (p : Γ' , [] ⟨ τ ⟩ split Γ )
                  → (V : Γ' ⊢V⦂ [ τ ] A)
                  → (M : Γ' ⟨ τ ⟩ ∷ [ τ ] A ⊢C⦂ C)
                  ------------------------------------------------------
                  → Γ ⊢C⦂ C-rename                                                     -- M[V/y]
                            (eq-ren (split-≡ p))                                       
                            (M [ Hd ↦ V-rename                                         
                                        (⟨⟩-mon-ren z≤n ∘ʳ ⟨⟩-eta⁻¹-ren)               
                                        V ]c)                                          
                      == unbox p ≤-refl                                               -- unbox V to x in M[box x/y]                             
                           V
                           (C-rename (eq-ren (split-≡ (split-∷ p)))
                             ((C-rename
                                (exch-ren ∘ʳ wk-ren) M)
                                [ Hd ↦ box (var (Tl-⟨⟩ Hd)) ]c))

    -- coercion equations
    
    coerce-refl : ∀ {A τ}
                → (M : Γ ⟨ τ ∸ τ ⟩ ⊢C⦂ A ‼ τ)
                -----------------------------------------------------------
                → Γ ⊢C⦂ coerce ≤-refl M
                    == C-rename
                         (⟨⟩-eta-ren ∘ʳ ⟨⟩-mon-ren (≤-reflexive (n∸n≡0 τ)))
                         M

    coerce-trans : ∀ {A τ τ' τ''}
                 → (p : τ ≤ τ')
                 → (q : τ' ≤ τ'')
                 → (M : Γ ⟨ τ'' ∸ τ' ⟩ ⟨ τ' ∸ τ ⟩ ⊢C⦂ A ‼ τ)
                 -----------------------------------------------------------
                 → Γ ⊢C⦂ coerce q (coerce p M)
                     == coerce (≤-trans p q)
                          (C-rename
                            (⟨⟩-mon-ren
                              (≤-trans
                                (≤-reflexive (sym (+-∸-assoc (τ'' ∸ τ') p)))
                                (∸-monoˡ-≤ τ (≤-reflexive (m∸n+n≡m q))))
                             ∘ʳ ⟨⟩-mu⁻¹-ren)
                            M)

  infix 18 _⊢C⦂_==_

  -- TODO: consider also adding some additional equations, such as 
  --       coerce in 2nd component of seq. comp. and coerce in perform;
  --       the currently selected equations are based on how the small
  --       step operational semantics would look like for coerce
