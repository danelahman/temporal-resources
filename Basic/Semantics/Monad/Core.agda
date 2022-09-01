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

open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad.Core where

-- Interpretation of ground types
---------------------------------

⟦_⟧ᵍ : GType → TSet
⟦ Base B ⟧ᵍ   = ConstTSet (BaseSet B)
⟦ Unit ⟧ᵍ     = 𝟙ᵗ
⟦ Empty ⟧ᵍ    = 𝟘ᵗ
⟦ [ τ ]ᵍ A ⟧ᵍ = [ τ ]ᵒ ⟦ A ⟧ᵍ


-- The free graded monad generated by the operations in Op
----------------------------------------------------------

-- Object mapping and time-monotonicity

mutual

  data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where

    leaf  : ∀ {t}
          → carrier A t
          → Tˢ A 0 t
       
    node  : ∀ {τ t}
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
     
    delay : ∀ {τ' t}
          → (τ : Time)
          → Tˢ A τ' (t + τ)
          → Tˢ A (τ + τ') t


  Tˢ-≤t : ∀ {A τ t t'} → t ≤ t' → Tˢ A τ t → Tˢ A τ t'
  Tˢ-≤t {A} p (leaf v) =
    leaf (monotone A p v)
  Tˢ-≤t p (node op v k k-nat) =
    node op
      (monotone (⟦ param op ⟧ᵍ) p v)
      (λ q y → k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y)
      (λ p q y →
        trans
          (cong (λ q → k q (monotone ⟦ arity op ⟧ᵍ p y)) (≤-irrelevant _ _))
          (k-nat _ _ y))
  Tˢ-≤t p (delay τ k) =
    delay τ (Tˢ-≤t (+-monoˡ-≤ τ p) k)


-- Reflexivity and transitivity of time-monotonicity

Tˢ-≤t-refl : ∀ {A τ t} → (c : Tˢ A τ t) → Tˢ-≤t ≤-refl c ≡ c
Tˢ-≤t-refl {A} (leaf v) =
  cong leaf (monotone-refl A v)
Tˢ-≤t-refl {A = A} {t = t} (node {τ = τ} op v k k-nat) =
  dcong₃ (node op)
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
Tˢ-≤t-refl (delay τ k) =
  cong (delay τ)
    (trans
      (cong (λ p → Tˢ-≤t p k) (≤-irrelevant _ _))
      (Tˢ-≤t-refl k))

Tˢ-≤t-trans : ∀ {A τ t t' t''}
            → (p : t ≤ t') → (q : t' ≤ t'') → (c : Tˢ A τ t)
            → Tˢ-≤t q (Tˢ-≤t p c) ≡ Tˢ-≤t (≤-trans p q) c
Tˢ-≤t-trans {A} p q (leaf v) =
  cong leaf (monotone-trans A p q v)
Tˢ-≤t-trans {A = A} {t'' = t''} p q (node {τ = τ} op v k k-nat) =
  dcong₃ (node op)
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
Tˢ-≤t-trans p q (delay τ k) =
  cong (delay τ)
    (trans
      (Tˢ-≤t-trans (+-monoˡ-≤ τ p) (+-monoˡ-≤ τ q) k)
      (cong (λ p → Tˢ-≤t p k) (≤-irrelevant _ _)))


-- Functorial action

mutual

  {-# TERMINATING #-}

  -- For now, telling Agda manually that the definitions below are
  -- terminating. The problem lies in Agda not seeing that uses of
  -- `Tˢᶠ` in the types involved in the `node op ...` case are indeed
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
  Tˢᶠ f (node op v k k-nat) =
    node op v
      (λ p y → Tˢᶠ f (k p y))
      (λ p q y →
        trans
          (cong (Tˢᶠ f) (k-nat p q y))
          (Tˢᶠ-≤t-nat f p (k q y)))    
  Tˢᶠ f (delay τ k) =
    delay τ (Tˢᶠ f k)

  Tˢᶠ-≤t-nat : ∀ {A B τ} → (f : A →ᵗ B) → {t t' : ℕ}
             → (p : t ≤ t') → (c : Tˢ A τ t)
             → Tˢᶠ f (Tˢ-≤t p c) ≡ Tˢ-≤t p (Tˢᶠ f c)
  Tˢᶠ-≤t-nat f p (leaf v) =
    cong leaf (map-nat f p v)
  Tˢᶠ-≤t-nat f p (node op v k k-nat) =
    dcong₃ (node op)
      refl
      refl
      (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
  Tˢᶠ-≤t-nat f p (delay τ k) =
    cong (delay τ) (Tˢᶠ-≤t-nat f (+-monoˡ-≤ τ p) k)

Tˢᶠ-idᵗ : ∀ {A τ} → {t : Time}
        → (c : Tˢ A τ t)
        → Tˢᶠ idᵗ c ≡ c
Tˢᶠ-idᵗ (leaf v) =
  cong leaf (idᵗ-reveal v)
Tˢᶠ-idᵗ (node op v k k-nat) =
  dcong₂ (node op v)
    (ifun-ext (fun-ext (λ p → fun-ext (λ y → Tˢᶠ-idᵗ (k p y)))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢᶠ-idᵗ (delay τ k) =
  cong (delay τ) (Tˢᶠ-idᵗ k)

Tˢᶠ-∘ᵗ : ∀ {A B C τ}
       → (g : B →ᵗ C)
       → (f : A →ᵗ B)
       → {t : Time}
       → (c : Tˢ A τ t)
       → Tˢᶠ (g ∘ᵗ f) c ≡ Tˢᶠ g (Tˢᶠ f c)
Tˢᶠ-∘ᵗ g f (leaf v) =
  cong leaf (∘ᵗ-reveal g f v)
Tˢᶠ-∘ᵗ g f (node op v k k-nat) =
  dcong₂ (node op v)
    (ifun-ext (fun-ext (λ p → (fun-ext (λ y → Tˢᶠ-∘ᵗ g f (k p y))))))
    (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))
Tˢᶠ-∘ᵗ g f (delay τ k) =
  cong (delay τ) (Tˢᶠ-∘ᵗ g f k)


-- Packaging it all up into a functor on TSet

Tᵒ : TSet → Time → TSet
Tᵒ A τ = tset (Tˢ A τ) Tˢ-≤t Tˢ-≤t-refl Tˢ-≤t-trans
 
Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ
Tᶠ f = tset-map (Tˢᶠ f) (Tˢᶠ-≤t-nat f)

Tᶠ-idᵗ : ∀ {A τ}
       → Tᶠ {A} {A} {τ} idᵗ ≡ᵗ idᵗ
Tᶠ-idᵗ =
  eqᵗ (λ c →
    trans
      (Tˢᶠ-idᵗ c)
      (sym (idᵗ-reveal c)))

Tᶠ-∘ᵗ : ∀ {A B C τ}
      → (g : B →ᵗ C)
      → (f : A →ᵗ B)
      → Tᶠ {A} {C} {τ} (g ∘ᵗ f) ≡ᵗ Tᶠ g ∘ᵗ Tᶠ f
Tᶠ-∘ᵗ g f =
  eqᵗ (λ c →
    trans
      (Tˢᶠ-∘ᵗ g f c)
      (sym (∘ᵗ-reveal (Tᶠ g) (Tᶠ f) c)))


-- "subst" for time-gradings

τ-subst : ∀ {A τ τ'}
        → τ ≡ τ'
        → {t : Time}
        → Tˢ A τ t
        → Tˢ A τ' t
τ-subst refl c = c

τ-subst-≤t : ∀ {A τ τ' t t'}
           → (p : τ ≡ τ')
           → (q : t ≤ t')
           → (c : Tˢ A τ t)
           → τ-subst p (Tˢ-≤t q c) ≡ Tˢ-≤t q (τ-subst p c)
τ-subst-≤t refl q c = refl

τ-subst-trans : ∀ {A τ τ' τ'' t}
              → (p : τ ≡ τ')
              → (q : τ' ≡ τ'')
              → (c : Tˢ A τ t)
              → τ-subst q (τ-subst p c) ≡ τ-subst (trans p q) c
τ-subst-trans refl refl c = refl

τ-substᵀ : ∀ {A τ τ'}
         → τ ≡ τ'
         → Tᵒ A τ →ᵗ Tᵒ A τ'
τ-substᵀ p =
  tset-map
    (τ-subst p)
    (τ-subst-≤t p)

τ-subst-Tˢᶠ : ∀ {A B τ τ' t}
            → (p : τ ≡ τ')
            → (f : A →ᵗ B)
            → (c : Tˢ A τ t)
            → τ-subst p (Tˢᶠ f c) ≡ Tˢᶠ f (τ-subst p c)
τ-subst-Tˢᶠ refl f c = refl

τ-subst-delay : ∀ {A τ' τ'' t}
              → (τ : Time)
              → (p : τ' ≡ τ'')
              → (c : Tˢ A τ' (t + τ))
              → τ-subst (cong (τ +_) p) (delay τ c)
              ≡ delay τ (τ-subst p c)
τ-subst-delay τ refl c = refl

τ-subst-node : ∀ {A τ τ' t}
             → (p : τ ≡ τ')
             → (op : Op)
             → (v : carrier ⟦ param op ⟧ᵍ t)
             → (k : {t' : Time} → t + op-time op ≤ t' → carrier ⟦ arity op ⟧ᵍ t' → Tˢ A τ t')
             → (k-nat : {t' t'' : Time} (q : t' ≤ t'') (r : t + op-time op ≤ t')
                        (y : carrier ⟦ arity op ⟧ᵍ t') →
                        k (≤-trans r q) (monotone ⟦ arity op ⟧ᵍ q y) ≡ Tˢ-≤t q (k r y))
             → τ-subst
                 (cong (op-time op +_) p)
                 (node op v k k-nat)
             ≡ node op v
                 (λ q y →
                   τ-subst p (k q y))
                 (λ q r y →
                   trans
                     (cong (τ-subst p) (k-nat q r y))
                     (τ-subst-≤t p q (k r y)))
τ-subst-node refl op v k k-nat =
  dcong₂ (node op v)
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
  eqᵗ (λ c →
    trans
      (∘ᵗ-reveal ηᵀ f c)
      (sym (∘ᵗ-reveal (Tᶠ f) ηᵀ c)))


-- Multiplication

mutual

  {-# TERMINATING #-}

  μˢ : ∀ {A τ τ'} → {t : Time}
     → Tˢ (Tᵒ A τ') τ t → Tˢ A (τ + τ') t
  μˢ (leaf c) =
    c
  μˢ (node op v k k-nat) =
    τ-subst
      (sym (+-assoc (op-time op) _ _))
      (node op v
        (λ p y → μˢ (k p y))
        (λ p q y →
          trans
            (cong μˢ (k-nat p q y))
            (μˢ-≤t-nat p (k q y))))
  μˢ (delay τ k) =
    τ-subst (sym (+-assoc τ _ _)) (delay τ (μˢ k))

  μˢ-≤t-nat : ∀ {A τ τ'} → {t t' : ℕ}
          → (p : t ≤ t')
          → (c : Tˢ (Tᵒ A τ') τ t)
          → μˢ (Tˢ-≤t p c) ≡ Tˢ-≤t p (μˢ c)
  μˢ-≤t-nat p (leaf v) =
    refl
  μˢ-≤t-nat p (node op v k k-nat) =
    trans
      (cong (τ-subst (sym (+-assoc (op-time op) _ _)))
        (dcong₂ (node op (monotone ⟦ param op ⟧ᵍ p v))
          refl
          (ifun-ext (ifun-ext (fun-ext (λ q → fun-ext (λ r → fun-ext (λ y → uip))))))))
      (τ-subst-≤t (sym (+-assoc (op-time op) _ _)) p _)
  μˢ-≤t-nat p (delay τ k) =
    trans
      (cong
        (τ-subst (sym (+-assoc τ _ _)))
        (cong (delay τ) (μˢ-≤t-nat (+-monoˡ-≤ τ p) k)))
      (τ-subst-≤t (sym (+-assoc τ _ _)) p (delay τ (μˢ k)))

μˢ-nat : ∀ {A B τ τ'}
       → (f : A →ᵗ B)
       → {t : Time}
       → (c : Tˢ (Tᵒ A τ') τ t)
       → μˢ (Tˢᶠ (Tᶠ f) c) ≡ Tˢᶠ f (μˢ c)
μˢ-nat f (leaf v) =
  refl
μˢ-nat f (node op v k k-nat) =
  trans
    (cong (τ-subst (sym (+-assoc (op-time op) _ _)))
      (dcong₂ (node op v)
        (ifun-ext (fun-ext (λ p → fun-ext (λ y → μˢ-nat f (k p y)))))
        (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
    (τ-subst-Tˢᶠ (sym (+-assoc (op-time op) _ _)) f _)
μˢ-nat f (delay τ k) =
  trans
    (cong (τ-subst (sym (+-assoc τ _ _)))
      (cong (delay τ)
        (μˢ-nat f k)))
    (τ-subst-Tˢᶠ (sym (+-assoc τ _ _)) f (delay τ (μˢ k)))

μᵀ : ∀ {A τ τ'}
   → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')
μᵀ = tset-map μˢ μˢ-≤t-nat

μᵀ-nat : ∀ {A B τ τ'}
       → (f : A →ᵗ B)
       → μᵀ {τ = τ} {τ' = τ'} ∘ᵗ Tᶠ (Tᶠ f) ≡ᵗ Tᶠ f ∘ᵗ μᵀ
μᵀ-nat f =
  eqᵗ (λ c →
    trans
      (∘ᵗ-reveal μᵀ (Tᶠ (Tᶠ f)) c)
      (trans
        (μˢ-nat f c)
        (sym (∘ᵗ-reveal (Tᶠ f) μᵀ c))))


-- Monad laws (TODO)

μᵀ-identity₁ : ∀ {A τ}
             →  μᵀ {τ = 0} {τ' = τ} ∘ᵗ ηᵀ {Tᵒ A τ}
             ≡ᵗ idᵗ
μᵀ-identity₁ =
  eqᵗ (λ c →
    trans (∘ᵗ-reveal μᵀ ηᵀ c) (sym (idᵗ-reveal c)))

μˢ-identity₂ : ∀ {A τ}
             → {t : Time}
             → (c : Tˢ A τ t)
             → μˢ {τ = τ} {τ' = 0} (Tˢᶠ (ηᵀ {A}) c)
             ≡ τ-subst (sym (+-identityʳ τ)) c
μˢ-identity₂ (leaf v) =
  refl
μˢ-identity₂ (node {τ} op v k k-nat) =
  trans
    (cong (τ-subst (sym (+-assoc (op-time op) τ 0)))
      (dcong₂ (node op v)
        {y₂ = λ p q y →
          trans
            (cong (τ-subst (sym (+-identityʳ τ)))
              (k-nat p q y))
            (τ-subst-≤t _ _ (k q y))}
        (ifun-ext (fun-ext (λ p → fun-ext (λ y → μˢ-identity₂ (k p y)))))
        (ifun-ext (ifun-ext (fun-ext (λ p → fun-ext (λ q → fun-ext (λ y → uip))))))))
    (trans
      (cong (τ-subst (sym (+-assoc (op-time op) τ 0)))
        (sym (τ-subst-node _ op v k k-nat)))
      (trans
        (τ-subst-trans _ (sym (+-assoc (op-time op) τ 0)) (node op v k k-nat))
        (cong (λ p → τ-subst p (node op v k k-nat)) uip)))
μˢ-identity₂ (delay {τ'} τ k) =
  trans
    (cong (τ-subst (sym (+-assoc τ τ' 0)))
      (cong (delay τ)
        (μˢ-identity₂ k)))
    (trans
      (cong (τ-subst (sym (+-assoc τ τ' 0)))
        (sym (τ-subst-delay τ _ k)))
      (trans
        (τ-subst-trans _ (sym (+-assoc τ τ' 0)) (delay τ k))
        (cong (λ p → τ-subst p (delay τ k)) uip)))

μᵀ-identity₂ : ∀ {A τ}
             →  μᵀ {τ = τ} {τ' = 0} ∘ᵗ Tᶠ (ηᵀ {A})
             ≡ᵗ τ-substᵀ (sym (+-identityʳ τ))
μᵀ-identity₂ =
  eqᵗ (λ c →
    trans
      (∘ᵗ-reveal μᵀ (Tᶠ ηᵀ) c)
      (μˢ-identity₂ c))

























---------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------


{-


-- Candidate for object-mapping of the underlying functor to support quotienting by delay equations
-- NOTE: quick sketch, does not include naturality condition for operation nodes


mutual
  
  data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where  -- 1st time index (τ) is the duration of the computation (its time-grading)
                                                            -- 2nd time index (t) is the corresponding TSets' time-index (presheaf index)
    delay : ∀ {τ' t}
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
     
    node  : ∀ {τ t}
          → (op : Op)
          → carrier ⟦ param op ⟧ᵍ t
          → ({t' : Time} → t + op-time op ≤ t'
                         → carrier ⟦ arity op ⟧ᵍ t'
                         → Tˢ A τ t')
          → Tᶜˢ A (op-time op + τ) t

-}
