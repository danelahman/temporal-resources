---------------------------------------------------------
-- Free graded monad generated by algebraic operations --
---------------------------------------------------------

-- Note: A version of the monad that is not quotioned by
--       the delay equations (identity and composition)

module Semantics.Model.Examples.TSets.Monad.Core where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Unit hiding (_≤_)

open import Semantics.Model.BaseGroundTypes

open import Semantics.Model.Examples.TSets.TSets
open import Semantics.Model.Examples.TSets.Modality.Future
open import Semantics.Model.Examples.TSets.Modality.Past
open import Semantics.Model.Examples.TSets.BaseGroundTypes

open import Util.Equality
open import Util.Operations
open import Util.Time

open BaseGroundTypes TSetTyp public

-- The free graded monad generated by the operations in Op
----------------------------------------------------------

-- Object mapping and time-monotonicity

mutual

  data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where

    leaf  : ∀ {t}
          → carrier A t
          → Tˢ A 0 t
       
    op-node  : ∀ {τ t}
             → (op : Op)
             → carrier ⟦ param op ⟧ᵍ t
             → (k : {t' : Time} → t + op-time op ≤ t'
                                → carrier ⟦ arity op ⟧ᵍ t'
                                → Tˢ A τ t')
             → ({t' t'' : Time} → (p : t' ≤ t'')                                       -- time-naturality of continuation
                                → (q : t + op-time op ≤ t')
                                → (y : carrier ⟦ arity op ⟧ᵍ t')
                                → k (≤-trans q p) (monotone (⟦ arity op ⟧ᵍ) p y)
                                ≡ Tˢ-≤t p (k q y))
             → Tˢ A (op-time op + τ) t
     
    delay-node : ∀ {τ' t}
               → (τ : Time)
               → Tˢ A τ' (t + τ)
               → Tˢ A (τ + τ') t


  Tˢ-≤t : ∀ {A τ t t'} → t ≤ t' → Tˢ A τ t → Tˢ A τ t'
  Tˢ-≤t {A} p (leaf v) =
    leaf (monotone A p v)
  Tˢ-≤t p (op-node op v k k-nat) =
    op-node op
      (monotone (⟦ param op ⟧ᵍ) p v)
      (λ q y → k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y)
      (λ p q y →
        trans
          (cong (λ q → k q (monotone ⟦ arity op ⟧ᵍ p y)) (≤-irrelevant _ _))
          (k-nat _ _ y))
  Tˢ-≤t p (delay-node τ k) =
    delay-node τ (Tˢ-≤t (+-monoˡ-≤ τ p) k)


-- Reflexivity and transitivity of time-monotonicity

Tˢ-≤t-refl : ∀ {A τ t} → (c : Tˢ A τ t) → Tˢ-≤t ≤-refl c ≡ c
Tˢ-≤t-refl {A} (leaf v) =
  cong leaf (monotone-refl A v)
Tˢ-≤t-refl {A = A} {t = t} (op-node {τ = τ} op v k k-nat) =
  dcong₃ (op-node op)
    (monotone-refl ⟦ param op ⟧ᵍ v)
    (ifun-ext (fun-ext (λ p → fun-ext (λ y →
      trans
        (cong (λ (k : {t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A τ t') → k p y)
          {subst (λ _ → {t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A τ t')
              (monotone-refl ⟦ param op ⟧ᵍ v)
              (λ q → k (≤-trans (+-monoˡ-≤ (op-time op) ≤-refl) q))}
          (subst-const _ (monotone-refl ⟦ param op ⟧ᵍ v) _))
        (cong (λ p → k p y) (≤-irrelevant _ _))))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢ-≤t-refl (delay-node τ k) =
  cong (delay-node τ)
    (trans
      (cong (λ p → Tˢ-≤t p k) (≤-irrelevant _ _))
      (Tˢ-≤t-refl k))

Tˢ-≤t-trans : ∀ {A τ t t' t''}
            → (p : t ≤ t') → (q : t' ≤ t'') → (c : Tˢ A τ t)
            → Tˢ-≤t q (Tˢ-≤t p c) ≡ Tˢ-≤t (≤-trans p q) c
Tˢ-≤t-trans {A} p q (leaf v) =
  cong leaf (monotone-trans A p q v)
Tˢ-≤t-trans {A = A} {t'' = t''} p q (op-node {τ = τ} op v k k-nat) =
  dcong₃ (op-node op)
    (monotone-trans (⟦ param op ⟧ᵍ) p q v)
    (ifun-ext (fun-ext (λ r → fun-ext (λ y →
      trans
        (cong (λ (k : {t''' : Time} → t'' + op-time op ≤ t''' → carrier ⟦ arity op ⟧ᵍ t''' → Tˢ A τ t''') → k r y)
          {subst
            (λ _ → {t' = t''' : Time} → t'' + op-time op ≤ t''' → carrier ⟦ arity op ⟧ᵍ t''' → Tˢ A τ t''')
            (monotone-trans ⟦ param op ⟧ᵍ p q v)
            (λ r → k (≤-trans (+-monoˡ-≤ (op-time op) p) (≤-trans (+-monoˡ-≤ (op-time op) q) r)))}
          (subst-const _ (monotone-trans ⟦ param op ⟧ᵍ p q v) _))
        (cong (λ p → k p y) (≤-irrelevant _ _))))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢ-≤t-trans p q (delay-node τ k) =
  cong (delay-node τ)
    (trans
      (Tˢ-≤t-trans (+-monoˡ-≤ τ p) (+-monoˡ-≤ τ q) k)
      (cong (λ p → Tˢ-≤t p k) (≤-irrelevant _ _)))


-- Functorial action

mutual

  {-# TERMINATING #-}

  -- For now, telling Agda manually that the definitions below are
  -- terminating. The problem lies in Agda not seeing that uses of
  -- `Tˢᶠ` in the types involved in the `op-node op ...` case are indeed
  -- applied to smaller arguments when calling the simultaneously
  -- defined function `Tˢᶠ-≤t-nat` to fill a hole of type
  --
  --   `Tˢᶠ f (Tˢ-≤t p (k q y)) ≡ Tˢ-≤t p (Tˢᶠ f (k q y))`
  --
  -- Here `Tˢ-≤t` is masking that `k q y` and thus `Tˢ-≤t p (k q y)` 
  -- are in fact smaller trees.
  --
  -- Possible solutions include additionally indexing the trees by
  -- their heights, using sized types (when they become consistent),
  -- or moving the `k-nat` condition into a separate extrinsic
  -- predicate. The latter involves duplicating all definitions.
  --
  -- For now not implementing any of those workarounds to keep the
  -- presheaf model clean and not polluted by formalisation artefacts.
  -- 
  -- The other uses of {-# TERMINATING #-} in this and related `Monad`
  -- modules are included because of analogous reasons.

  Tˢᶠ : ∀ {A B τ} → A →ᵗ B → {t : Time} → Tˢ A τ t → Tˢ B τ t
  Tˢᶠ f (leaf v) =
    leaf (map-carrier f v)
  Tˢᶠ f (op-node op v k k-nat) =
    op-node op v
      (λ p y → Tˢᶠ f (k p y))
      (λ p q y →
        trans
          (cong (Tˢᶠ f) (k-nat p q y))
          (Tˢᶠ-≤t-nat f p (k q y)))    
  Tˢᶠ f (delay-node τ k) =
    delay-node τ (Tˢᶠ f k)

  Tˢᶠ-≤t-nat : ∀ {A B τ} → (f : A →ᵗ B) → {t t' : ℕ}
             → (p : t ≤ t') → (c : Tˢ A τ t)
             → Tˢᶠ f (Tˢ-≤t p c) ≡ Tˢ-≤t p (Tˢᶠ f c)
  Tˢᶠ-≤t-nat f p (leaf v) =
    cong leaf (map-nat f p v)
  Tˢᶠ-≤t-nat f p (op-node op v k k-nat) =
    dcong₃ (op-node op)
      refl
      refl
      (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
  Tˢᶠ-≤t-nat f p (delay-node τ k) =
    cong (delay-node τ) (Tˢᶠ-≤t-nat f (+-monoˡ-≤ τ p) k)

Tˢᶠ-idᵗ : ∀ {A τ} → {t : Time}
        → (c : Tˢ A τ t)
        → Tˢᶠ idᵗ c ≡ c
Tˢᶠ-idᵗ (leaf v) =
  refl
Tˢᶠ-idᵗ (op-node op v k k-nat) =
  dcong₂ (op-node op v)
    (ifun-ext (fun-ext (λ p → fun-ext (λ y → Tˢᶠ-idᵗ (k p y)))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢᶠ-idᵗ (delay-node τ k) =
  cong (delay-node τ) (Tˢᶠ-idᵗ k)

Tˢᶠ-∘ᵗ : ∀ {A B C τ}
       → (g : B →ᵗ C)
       → (f : A →ᵗ B)
       → {t : Time}
       → (c : Tˢ A τ t)
       → Tˢᶠ (g ∘ᵗ f) c ≡ Tˢᶠ g (Tˢᶠ f c)
Tˢᶠ-∘ᵗ g f (leaf v) =
  refl
Tˢᶠ-∘ᵗ g f (op-node op v k k-nat) =
  dcong₂ (op-node op v)
    (ifun-ext (fun-ext (λ p → (fun-ext (λ y → Tˢᶠ-∘ᵗ g f (k p y))))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢᶠ-∘ᵗ g f (delay-node τ k) =
  cong (delay-node τ) (Tˢᶠ-∘ᵗ g f k)


-- Packaging it all up into a functor on TSet

Tᵒ : TSet → Time → TSet
Tᵒ A τ = tset (Tˢ A τ) Tˢ-≤t Tˢ-≤t-refl Tˢ-≤t-trans
 
Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ
Tᶠ f = tset-map (Tˢᶠ f) (Tˢᶠ-≤t-nat f)

Tᶠ-idᵗ : ∀ {A τ}
       → Tᶠ {A} {A} {τ} idᵗ ≡ᵗ idᵗ
Tᶠ-idᵗ =
  eqᵗ Tˢᶠ-idᵗ

Tᶠ-∘ᵗ : ∀ {A B C τ}
      → (g : B →ᵗ C)
      → (f : A →ᵗ B)
      → Tᶠ {A} {C} {τ} (g ∘ᵗ f) ≡ᵗ Tᶠ g ∘ᵗ Tᶠ f
Tᶠ-∘ᵗ g f =
  eqᵗ (Tˢᶠ-∘ᵗ g f)


-- "subst" for time-gradings

τ-substˢ : ∀ {A τ τ'}
         → τ ≡ τ'
         → {t : Time}
         → Tˢ A τ t
         → Tˢ A τ' t
τ-substˢ refl c = c

τ-substˢ-≤t : ∀ {A τ τ' t t'}
            → (p : τ ≡ τ')
            → (q : t ≤ t')
            → (c : Tˢ A τ t)
            → τ-substˢ p (Tˢ-≤t q c) ≡ Tˢ-≤t q (τ-substˢ p c)
τ-substˢ-≤t refl q c =
  refl

τ-substˢ-trans : ∀ {A τ τ' τ'' t}
               → (p : τ ≡ τ')
               → (q : τ' ≡ τ'')
               → (c : Tˢ A τ t)
               → τ-substˢ q (τ-substˢ p c) ≡ τ-substˢ (trans p q) c
τ-substˢ-trans refl refl c =
  refl

τ-substᵀ : ∀ {A τ τ'}
         → τ ≡ τ'
         → Tᵒ A τ →ᵗ Tᵒ A τ'
τ-substᵀ p =
  tset-map
    (τ-substˢ p)
    (τ-substˢ-≤t p)

τ-substᵀ-refl : ∀ {A τ}
              → τ-substᵀ {A} {τ} refl
             ≡ᵗ idᵗ
τ-substᵀ-refl =
  eqᵗ (λ x → refl)
 
τ-substᵀ-trans : ∀ {A τ τ' τ''}
               → (p : τ ≡ τ')
               → (q : τ' ≡ τ'')
               → τ-substᵀ q ∘ᵗ τ-substᵀ p
              ≡ᵗ τ-substᵀ {A} (trans p q)
τ-substᵀ-trans p q = 
  eqᵗ (τ-substˢ-trans p q)

τ-substˢ-Tˢᶠ : ∀ {A B τ τ' t}
             → (p : τ ≡ τ')
             → (f : A →ᵗ B)
             → (c : Tˢ A τ t)
             → τ-substˢ p (Tˢᶠ f c) ≡ Tˢᶠ f (τ-substˢ p c)
τ-substˢ-Tˢᶠ refl f c =
  refl

τ-substˢ-delay : ∀ {A τ' τ'' t}
               → (τ : Time)
               → (p : τ' ≡ τ'')
               → (c : Tˢ A τ' (t + τ))
               → τ-substˢ (cong (τ +_) p) (delay-node τ c)
               ≡ delay-node τ (τ-substˢ p c)
τ-substˢ-delay τ refl c =
  refl

τ-substˢ-op : ∀ {A τ τ' t}
              → (p : τ ≡ τ')
              → (op : Op)
              → (v : carrier ⟦ param op ⟧ᵍ t)
              → (k : {t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A τ t')
              → (k-nat : {t' t'' : Time} (q : t' ≤ t'') (r : t + op-time op ≤ t')
                         (y : carrier ⟦ arity op ⟧ᵍ t') →
                         k (≤-trans r q) (monotone ⟦ arity op ⟧ᵍ q y) ≡ Tˢ-≤t q (k r y))
              → τ-substˢ
                  (cong (op-time op +_) p)
                  (op-node op v k k-nat)
              ≡ op-node op v
                  (λ q y →
                    τ-substˢ p (k q y))
                  (λ q r y →
                    trans
                      (cong (τ-substˢ p) (k-nat q r y))
                      (τ-substˢ-≤t p q (k r y)))
τ-substˢ-op refl op v k k-nat =
  dcong₂ (op-node op v)
    refl
    (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))


-- Unit

ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0
ηᵀ =
  tset-map
    (λ v → leaf v)
    (λ p v → refl)

ηᵀ-nat : ∀ {A B}
       → (f : A →ᵗ B)
       → ηᵀ ∘ᵗ f ≡ᵗ Tᶠ f ∘ᵗ ηᵀ
ηᵀ-nat f =
  eqᵗ (λ c → refl)


-- Multiplication

mutual

  {-# TERMINATING #-}

  μˢ : ∀ {A τ τ'} → {t : Time}
     → Tˢ (Tᵒ A τ') τ t → Tˢ A (τ + τ') t
  μˢ (leaf c) =
    c
  μˢ (op-node op v k k-nat) =
    τ-substˢ
      (sym (+-assoc (op-time op) _ _))
      (op-node op v
        (λ p y → μˢ (k p y))
        (λ p q y →
          trans
            (cong μˢ (k-nat p q y))
            (μˢ-≤t-nat p (k q y))))
  μˢ (delay-node τ k) =
    τ-substˢ (sym (+-assoc τ _ _)) (delay-node τ (μˢ k))

  μˢ-≤t-nat : ∀ {A τ τ'} → {t t' : ℕ}
          → (p : t ≤ t')
          → (c : Tˢ (Tᵒ A τ') τ t)
          → μˢ (Tˢ-≤t p c) ≡ Tˢ-≤t p (μˢ c)
  μˢ-≤t-nat p (leaf v) =
    refl
  μˢ-≤t-nat p (op-node op v k k-nat) =
    trans
      (cong (τ-substˢ (sym (+-assoc (op-time op) _ _)))
        (dcong₂ (op-node op (monotone ⟦ param op ⟧ᵍ p v))
          refl
          (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))))
      (τ-substˢ-≤t (sym (+-assoc (op-time op) _ _)) p _)
  μˢ-≤t-nat p (delay-node τ k) =
    trans
      (cong
        (τ-substˢ (sym (+-assoc τ _ _)))
        (cong (delay-node τ) (μˢ-≤t-nat (+-monoˡ-≤ τ p) k)))
      (τ-substˢ-≤t (sym (+-assoc τ _ _)) p (delay-node τ (μˢ k)))

μᵀ : ∀ {A τ τ'}
   → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')
μᵀ = tset-map μˢ μˢ-≤t-nat

μˢ-nat : ∀ {A B τ τ'}
       → (f : A →ᵗ B)
       → {t : Time}
       → (c : Tˢ (Tᵒ A τ') τ t)
       → μˢ (Tˢᶠ (Tᶠ f) c) ≡ Tˢᶠ f (μˢ c)
μˢ-nat f (leaf v) =
  refl
μˢ-nat f (op-node op v k k-nat) =
  trans
    (cong (τ-substˢ (sym (+-assoc (op-time op) _ _)))
      (dcong₂ (op-node op v)
        (ifun-ext (fun-ext (λ p → fun-ext (λ y → μˢ-nat f (k p y)))))
        (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
    (τ-substˢ-Tˢᶠ (sym (+-assoc (op-time op) _ _)) f _)
μˢ-nat f (delay-node τ k) =
  trans
    (cong (τ-substˢ (sym (+-assoc τ _ _)))
      (cong (delay-node τ)
        (μˢ-nat f k)))
    (τ-substˢ-Tˢᶠ (sym (+-assoc τ _ _)) f (delay-node τ (μˢ k)))

μᵀ-nat : ∀ {A B τ τ'}
       → (f : A →ᵗ B)
       → μᵀ {τ = τ} {τ' = τ'} ∘ᵗ Tᶠ (Tᶠ f) ≡ᵗ Tᶠ f ∘ᵗ μᵀ
μᵀ-nat f =
  eqᵗ (μˢ-nat f)

τ-substˢ-μˢ : ∀ {A τ τ' τ'' t}
           → (p : τ ≡ τ'')
           → (c : Tˢ (Tᵒ A τ') τ t)
           → τ-substˢ (cong (_+ τ') p) (μˢ c)
           ≡ μˢ (τ-substˢ p c)
τ-substˢ-μˢ refl c = refl


-- Monad laws

---- First identity law

μᵀ-identity₁ : ∀ {A τ}
             →  μᵀ {τ = 0} {τ' = τ} ∘ᵗ ηᵀ {Tᵒ A τ} ≡ᵗ idᵗ
μᵀ-identity₁ =
  eqᵗ (λ c → refl)

---- Second identity law

μˢ-identity₂ : ∀ {A τ}
             → {t : Time}
             → (c : Tˢ A τ t)
             → μˢ {τ = τ} {τ' = 0} (Tˢᶠ (ηᵀ {A}) c)
             ≡ τ-substˢ (sym (+-identityʳ τ)) c
μˢ-identity₂ (leaf v) =
  refl
μˢ-identity₂ (op-node {τ} op v k k-nat) =
  trans
    (cong (τ-substˢ (sym (+-assoc (op-time op) τ 0)))
      (dcong₂ (op-node op v)
        {y₂ = λ p q y →
          trans
            (cong (τ-substˢ (sym (+-identityʳ τ)))
              (k-nat p q y))
            (τ-substˢ-≤t _ _ (k q y))}
        (ifun-ext (fun-ext (λ p → fun-ext (λ y → μˢ-identity₂ (k p y)))))
        (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
    (trans
      (cong (τ-substˢ (sym (+-assoc (op-time op) τ 0)))
        (sym (τ-substˢ-op _ op v k k-nat)))
      (trans
        (τ-substˢ-trans _ (sym (+-assoc (op-time op) τ 0)) (op-node op v k k-nat))
        (cong (λ p → τ-substˢ p (op-node op v k k-nat)) uip)))
μˢ-identity₂ (delay-node {τ'} τ k) =
  trans
    (cong (τ-substˢ (sym (+-assoc τ τ' 0)))
      (cong (delay-node τ)
        (μˢ-identity₂ k)))
    (trans
      (cong (τ-substˢ (sym (+-assoc τ τ' 0)))
        (sym (τ-substˢ-delay τ _ k)))
      (trans
        (τ-substˢ-trans _ (sym (+-assoc τ τ' 0)) (delay-node τ k))
        (cong (λ p → τ-substˢ p (delay-node τ k)) uip)))

μᵀ-identity₂ : ∀ {A τ}
             →  μᵀ {τ = τ} {τ' = 0} ∘ᵗ Tᶠ (ηᵀ {A})
             ≡ᵗ τ-substᵀ (sym (+-identityʳ τ))
μᵀ-identity₂ =
  eqᵗ μˢ-identity₂

---- Associativity law

μˢ-assoc : ∀ {A τ τ' τ'' t}
         → (c : carrier (Tᵒ (Tᵒ (Tᵒ A τ'') τ') τ) t)
         → μˢ {A} {τ} {τ' + τ''} (Tˢᶠ μᵀ c)
         ≡ τ-substˢ (+-assoc τ τ' τ'') (μˢ (μˢ c))
μˢ-assoc (leaf v) =
  refl
μˢ-assoc {A} {τ' = τ'} {τ'' = τ''} (op-node {τ = τ} op v k k-nat) =
  trans
    (cong (τ-substˢ (sym (+-assoc (op-time op) τ (τ' + τ''))))
      (dcong₂ (op-node op v)
        {y₂ = λ p q y →
          trans
            (cong (τ-substˢ (+-assoc τ τ' τ''))
              (trans
                (cong (λ c → μˢ (μˢ c))
                  (k-nat p q y))
                (trans
                  (cong μˢ (μˢ-≤t-nat _ (k q y)))
                  (μˢ-≤t-nat _ (μˢ (k q y))))))
            (τ-substˢ-≤t _ _ (μˢ (μˢ (k q y))))}
        (ifun-ext (fun-ext (λ p → fun-ext (λ y → μˢ-assoc (k p y)))))
        (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
    (trans
      (trans
        (sym
          (cong (τ-substˢ (sym (+-assoc (op-time op) τ (τ' + τ''))))
            (τ-substˢ-op
              (+-assoc τ τ' τ'')
              op
              v
              (λ p y → μˢ (μˢ (k p y)))
              (λ p q y →
                trans
                  (cong (λ c → μˢ (μˢ c))
                    (k-nat p q y))
                  (trans
                    (cong μˢ (μˢ-≤t-nat _ (k q y)))
                    (μˢ-≤t-nat _ (μˢ (k q y))))))))
        (trans
          (τ-substˢ-trans
            (cong (_+_ (op-time op)) (+-assoc τ τ' τ''))
            (sym (+-assoc (op-time op) τ (τ' + τ''))) _)
          (trans
            (trans
              (cong₂
                (λ p c → τ-substˢ
                  {τ = op-time op + (τ + τ' + τ'')}
                  {τ' = op-time op + τ + (τ' + τ'')} p c)
                {trans (cong (_+_ (op-time op)) (+-assoc τ τ' τ''))
                  (sym (+-assoc (op-time op) τ (τ' + τ'')))}
                {trans (sym (+-assoc (op-time op) (τ + τ') τ''))
                  (trans (cong (_+ τ'') (sym (+-assoc (op-time op) τ τ')))
                    (+-assoc (op-time op + τ) τ' τ''))}
                uip
                (cong (op-node op v (λ p y → μˢ (μˢ (k p y))))
                  (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
              (sym
                (τ-substˢ-trans
                  (sym (+-assoc (op-time op) (τ + τ') τ''))
                  (trans (cong (_+ τ'') (sym (+-assoc (op-time op) τ τ')))
                    (+-assoc (op-time op + τ) τ' τ''))
                  _)))
            (sym
              (τ-substˢ-trans
                (cong (_+ τ'') (sym (+-assoc (op-time op) τ τ')))
                (+-assoc (op-time op + τ) τ' τ'') _)))))
      (cong (τ-substˢ (+-assoc (op-time op + τ) τ' τ''))
        (τ-substˢ-μˢ
          (sym (+-assoc (op-time op) τ τ'))
          (op-node op v
            (λ p y → μˢ (k p y))
            (λ p q y → trans (cong μˢ (k-nat p q y)) (μˢ-≤t-nat p (k q y)))))))
μˢ-assoc {A} {τ' = τ'} {τ'' = τ''} (delay-node {τ' = τ'''} τ k) =
  trans
    (cong (τ-substˢ (sym (+-assoc τ τ''' (τ' + τ''))))
      (cong (delay-node τ)
        (μˢ-assoc k)))
    (trans
      (cong (τ-substˢ (sym (+-assoc τ τ''' (τ' + τ''))))
        (sym (τ-substˢ-delay τ _ (μˢ (μˢ k)))))
      (trans
        (τ-substˢ-trans _ (sym (+-assoc τ τ''' (τ' + τ''))) (delay-node τ (μˢ (μˢ k))))
        (trans
          {j =
            τ-substˢ
              (+-assoc (τ + τ''') τ' τ'')
                (τ-substˢ {τ = τ + (τ''' + τ') + τ''} {τ' = τ + τ''' + τ' + τ''}
                  (cong (_+ τ'') (sym (+-assoc τ τ''' τ')))
                  (μˢ (delay-node τ (μˢ k))))}
          (trans
            (trans
              (cong (λ p → τ-substˢ p (delay-node τ (μˢ (μˢ k)))) uip)
              (sym (τ-substˢ-trans _ (+-assoc (τ + τ''') τ' τ'') (delay-node τ (μˢ (μˢ k))))))
            (cong (τ-substˢ (+-assoc (τ + τ''') τ' τ''))
              (sym (τ-substˢ-trans _ (cong (_+ τ'') (sym (+-assoc τ τ''' τ'))) (delay-node τ (μˢ (μˢ k)))))))
          (cong (τ-substˢ (+-assoc (τ + τ''') τ' τ''))
            (trans
              (trans
                (τ-substˢ-trans _ (cong (_+ τ'') (sym (+-assoc τ τ''' τ'))) (delay-node τ (μˢ (μˢ k))))
                (trans
                  (cong (λ p → τ-substˢ p (delay-node τ (μˢ (μˢ k)))) uip)
                  (sym (τ-substˢ-trans _ (cong (_+ τ'') (sym (+-assoc τ τ''' τ'))) (delay-node τ (μˢ (μˢ k)))))))
              (τ-substˢ-μˢ (sym (+-assoc τ τ''' τ')) (delay-node τ (μˢ k))))))))

μᵀ-assoc : ∀ {A τ τ' τ''}
         →  μᵀ {A} {τ} {τ' + τ''} ∘ᵗ Tᶠ μᵀ
         ≡ᵗ τ-substᵀ (+-assoc τ τ' τ'') ∘ᵗ (μᵀ ∘ᵗ μᵀ)
μᵀ-assoc {A} {τ} {τ'} {τ''} =
  eqᵗ μˢ-assoc




















---------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------


{-


-- Candidate for object-mapping of the underlying functor to support quotienting by delay-node equations
-- NOTE: quick sketch, does not include naturality condition for operation op-nodes


mutual
  
  data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where  -- 1st time index (τ) is the duration of the computation (its time-grading)
                                                            -- 2nd time index (t) is the corresponding TSets' time-index (presheaf index)
    delay-node : ∀ {τ' t}
          → (τ : Time)
          → 0 < τ
          → Tᶜˢ A τ' (t + τ)
          → Tˢ A (τ + τ') t
    comp  : ∀ {τ t}
          → Tᶜˢ A τ t
          → Tˢ A τ t
  data Tᶜˢ (A : TSet) : (τ : Time) → (t : Time) → Set where  -- 1st time index (τ) is the duration of the computation (its time-grading)
                                                             -- 2nd time index (t) is the corresponding TSets' time-index (presheaf index)
    leaf  : ∀ {t}
          → carrier A t
          → Tᶜˢ A 0 t
     
    op-node  : ∀ {τ t}
          → (op : Op)
          → carrier ⟦ param op ⟧ᵍ t
          → ({t' : Time} → t + op-time op ≤ t'
                         → carrier ⟦ arity op ⟧ᵍ t'
                         → Tˢ A τ t')
          → Tᶜˢ A (op-time op + τ) t

-}
