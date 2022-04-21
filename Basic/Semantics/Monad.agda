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

open import Util.HProp
open import Util.Equality
open import Util.Operations
open import Util.Time

module Semantics.Monad where

-- Interpretation of ground types as sets

⟦_⟧ᵍ : GType → Set
⟦ Base B ⟧ᵍ = BaseSet B
⟦ Unit ⟧ᵍ   = ⊤
⟦ Empty ⟧ᵍ  = ⊥

-- Object-mapping of the underlying functor

data Tˢ (A : TSet) : (τ : Time) → (t : Time) → Set where  -- 1st time index (τ) is the duration of the computation (its time-grading)
                                                          -- 2nd time index (t) is the corresponding TSets' time-index (modal time)
  leaf : ∀ {τ t}
       → carrier A (τ + t)
       → Tˢ A τ t

  node : ∀ {τ τ' t}
       → (op : Op)
       → carrier (ConstTSet ⟦ param op ⟧ᵍ) t
       → ({t' : Time} → t + op-time op ≤ t'
                      → carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'
                      → Tˢ A τ t')
       → τ' ≡ op-time op + τ                                    -- abstracting into a variable for easier recursive defs.
       → Tˢ A τ' t

-- Monotonicity wrt TSets' time-indices

Tˢ-≤t : ∀ {A τ t t'} → t ≤ t' → Tˢ A τ t → Tˢ A τ t'
Tˢ-≤t {A} p (leaf a) =
  leaf (monotone A (+-monoʳ-≤ _ p) a)
Tˢ-≤t {A} p (node op v k q) =
  node op v (λ q y → k (≤-trans (+-monoˡ-≤ (op-time op) p) q) y) q

Tˢ-≤t-refl : ∀ {A τ t} → (c : Tˢ A τ t) → Tˢ-≤t ≤-refl c ≡ c
Tˢ-≤t-refl {A} (leaf v) =
  cong
    leaf
    (trans
      (cong (λ p → monotone A p v) (≤-irrelevant _ ≤-refl))
      (monotone-refl A v))
Tˢ-≤t-refl {A} (node {τ} {τ'} {t} op v k p) =
  cong
    (λ (k : ({t' : Time} → t + op-time op ≤ t'
                         → carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'
                         → Tˢ A τ t'))
      → node op v k p)
    (ifun-ext (fun-ext (λ q → fun-ext (λ y →
      cong (λ q → k q y) (≤-irrelevant _ _)))))

Tˢ-≤t-trans : ∀ {A τ t t' t''}
            → (p : t ≤ t') → (q : t' ≤ t'') → (c : Tˢ A τ t)
            → Tˢ-≤t q (Tˢ-≤t p c) ≡ Tˢ-≤t (≤-trans p q) c

Tˢ-≤t-trans {A} p q (leaf v) =
  cong
    leaf
    (trans
      (monotone-trans A _ _ v)
      (cong (λ p → monotone A p v) (≤-irrelevant _ _)))
Tˢ-≤t-trans {A} p q (node op v k r) =
  cong (λ (k : ({t' : Time} → _ + op-time op ≤ t'
                            → carrier (ConstTSet ⟦ arity op ⟧ᵍ) t' → Tˢ A _ t'))
                            → node op (monotone (ConstTSet ⟦ param op ⟧ᵍ) (≤-trans p q) v) k r)
    (ifun-ext (fun-ext (λ s → fun-ext (λ y →
      cong (λ r → k r y) (≤-irrelevant _ _)))))

-- Extrinsic refinement of the object mapping to
-- operations whose continuations are natural

data Tˢ-natcont {A : TSet} : ∀ {τ t} → Tˢ A τ t → Set where

  natcont-leaf : ∀ {τ t v}
               → Tˢ-natcont (leaf {A} {τ} {t} v)

  natcont-node : ∀ {τ τ' t op x p}
                   {k : {t' : Time} → t + op-time op ≤ t'
                                    → carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'
                                    → Tˢ A τ t'}
               → ({t' t'' : Time} → (p : t + op-time op ≤ t')
                                  → (q : t' ≤ t'')
                                  → (y : carrier (ConstTSet ⟦ arity op ⟧ᵍ) t')
                                  → k (≤-trans p q) y ≡ Tˢ-≤t q (k p y))
               → ({t' : Time} → (q : t + op-time op ≤ t')
                              → (y : carrier (ConstTSet ⟦ arity op ⟧ᵍ) t')
                              → Tˢ-natcont (k q y))
               → Tˢ-natcont (node {A} {τ} {τ'} {t} op x k p)

Tˢʳ : TSet → Time → Time → Set
Tˢʳ A τ t = Σ[ c ∈ Tˢ A τ t ] Tˢ-natcont c

-- The extrinsic predicate is a proposition

Tˢ-natcont-isprop : ∀ {A τ t}
                  → {c : Tˢ A τ t}
                  → (p q : Tˢ-natcont c)
                  → p ≡ q

Tˢ-natcont-isprop natcont-leaf natcont-leaf = refl
Tˢ-natcont-isprop (natcont-node p q) (natcont-node p' q') =
  cong₂ natcont-node
    (ifun-ext (ifun-ext (fun-ext (λ r → fun-ext (λ s → fun-ext (λ y → uip))))))
    (ifun-ext (fun-ext (λ r → fun-ext (λ y → Tˢ-natcont-isprop (q r y) (q' r y)))))

-- Monotonicity wrt TSets' time-indices

Tˢ-≤t-natcont : ∀ {A τ t t'} → (p : t ≤ t') → {c : Tˢ A τ t}
              → Tˢ-natcont c
              → Tˢ-natcont (Tˢ-≤t p c)
Tˢ-≤t-natcont p natcont-leaf = natcont-leaf
Tˢ-≤t-natcont p {c = node op v k _} (natcont-node q r) =
  natcont-node
    (λ s t y →
      trans
        (cong (λ p → k p y) (≤-irrelevant _ _))
        (q _ _ y))
    (λ s y →
      subst
        Tˢ-natcont
        (sym (q _ _ y))
        (Tˢ-≤t-natcont s (r (+-monoˡ-≤ (op-time op) p) y)))

Tˢʳ-≤t : ∀ {A τ t t'} → t ≤ t' → Tˢʳ A τ t → Tˢʳ A τ t'
Tˢʳ-≤t p (c , q) = Tˢ-≤t p c , Tˢ-≤t-natcont p q 

Tˢʳ-≤t-refl : ∀ {A τ t} → (c : Tˢʳ A τ t)
            → Tˢʳ-≤t ≤-refl c ≡ c

Tˢʳ-≤t-refl (c , p) =
  dcong₂ _,_ (Tˢ-≤t-refl c) (Tˢ-natcont-isprop _ _)

Tˢʳ-≤t-trans : ∀ {A τ t t' t''}
             → (p : t ≤ t') → (q : t' ≤ t'') → (c : Tˢʳ A τ t)
             → Tˢʳ-≤t q (Tˢʳ-≤t p c) ≡ Tˢʳ-≤t (≤-trans p q) c

Tˢʳ-≤t-trans p q (c , r) =
  dcong₂ _,_ (Tˢ-≤t-trans p q c) (Tˢ-natcont-isprop _ _)

-- Functorial action on →ᵗ

Tˢᶠ : ∀ {A B τ} → A →ᵗ B → {t : Time} → Tˢ A τ t → Tˢ B τ t
Tˢᶠ f (leaf v)   =
  leaf (map-carrier f v)
Tˢᶠ f (node op v k q) =
  node op v (λ p y → Tˢᶠ f (k p y)) q

Tˢᶠ-nat : ∀ {A B τ} → (f : A →ᵗ B) → {t t' : ℕ}
        → (p : t ≤ t') → (c : Tˢ A τ t)
        → Tˢᶠ f (Tˢ-≤t p c) ≡ Tˢ-≤t p (Tˢᶠ f c)
        
Tˢᶠ-nat f p (leaf v) = cong leaf (map-nat f _ v)
Tˢᶠ-nat f p (node op v k q) = refl

Tˢᶠ-natcont : ∀ {A B τ} → (f : A →ᵗ B)
            → {t : Time} → {c : Tˢ A τ t}
            → Tˢ-natcont c
            → Tˢ-natcont (Tˢᶠ f c)
              
Tˢᶠ-natcont f natcont-leaf = natcont-leaf
Tˢᶠ-natcont f {c = node op v k _} (natcont-node p q) =
  natcont-node
    (λ r s y →
      trans (cong (Tˢᶠ f) (p r s y)) (Tˢᶠ-nat f s (k r y)))
    (λ r y → Tˢᶠ-natcont f (q r y))

Tˢʳᶠ : ∀ {A B τ} → A →ᵗ B → {t : Time} → Tˢʳ A τ t → Tˢʳ B τ t
Tˢʳᶠ f (c , p) = Tˢᶠ f c , Tˢᶠ-natcont f p

Tˢʳᶠ-nat : ∀ {A B τ} → (f : A →ᵗ B) → {t t' : ℕ}
         → (p : t ≤ t') → (c : Tˢʳ A τ t)
         → Tˢʳᶠ f (Tˢʳ-≤t p c) ≡ Tˢʳ-≤t p (Tˢʳᶠ f c)

Tˢʳᶠ-nat f p (c , q) =
  dcong₂ _,_ (Tˢᶠ-nat f p c) (Tˢ-natcont-isprop _ _)

-- Monotonicity wrt time-gradings

Tˢ-≤τ : ∀ {A τ τ' t} → τ ≤ τ' → Tˢ A τ t → Tˢ A τ' t
Tˢ-≤τ {A} p (leaf v) =
  leaf (monotone A (+-monoˡ-≤ _ p) v)
Tˢ-≤τ p (node op v k q) =
  node op v
    (λ r y →
      Tˢ-≤τ
        (proj₂ (proj₂ (n≡m+k≤n' (trans q (+-comm (op-time op) _)) p)))
        (k r y))
    (trans
      (proj₁ (proj₂ (n≡m+k≤n' (trans q (+-comm (op-time op) _)) p)))
      (+-comm _ (op-time op)))

Tˢ-≤τ-t-nat : ∀ {A τ τ'} → (p : τ ≤ τ') → {t t' : ℕ}
            → (q : t ≤ t') (c : Tˢ A τ t)
            → Tˢ-≤τ p (Tˢ-≤t q c) ≡ Tˢ-≤t q (Tˢ-≤τ p c)
Tˢ-≤τ-t-nat {A} p q (leaf v) =
  cong leaf
    (trans
      (monotone-trans A _ _ v)
      (trans
        (cong (λ r → monotone A r v) (≤-irrelevant _ _))
        (sym (monotone-trans A _ _ v))))
Tˢ-≤τ-t-nat p q (node op v k r) = refl

Tˢ-≤τ-natcont : ∀ {A τ τ' t} → (p : τ ≤ τ') → {c : Tˢ A τ t}
              → Tˢ-natcont c
              → Tˢ-natcont (Tˢ-≤τ p c)
Tˢ-≤τ-natcont p natcont-leaf = natcont-leaf
Tˢ-≤τ-natcont p {c = node {τ = τ} op v k u} (natcont-node q r) =
  natcont-node
    (λ s t y →
      trans
        (cong (Tˢ-≤τ _) (q s t y))
        (Tˢ-≤τ-t-nat
          (proj₂ (proj₂ (n≡m+k≤n' (trans u (+-comm (op-time op) τ)) p)))
          t
          (k s y)))
    (λ s y →
      Tˢ-≤τ-natcont
        (proj₂ (proj₂ (n≡m+k≤n' (trans u (+-comm (op-time op) τ)) p)))
        (r s y))

Tˢʳ-≤τ : ∀ {A τ τ' t} → τ ≤ τ' → Tˢʳ A τ t → Tˢʳ A τ' t
Tˢʳ-≤τ p (c , q) = Tˢ-≤τ p c , Tˢ-≤τ-natcont p q

Tˢʳ-≤τ-t-nat : ∀ {A τ τ'} → (p : τ ≤ τ') → {t t' : ℕ}
             → (q : t ≤ t') (c : Tˢʳ A τ t)
             → Tˢʳ-≤τ p (Tˢʳ-≤t q c) ≡ Tˢʳ-≤t q (Tˢʳ-≤τ p c)

Tˢʳ-≤τ-t-nat p q (c , r) =
  dcong₂ _,_ (Tˢ-≤τ-t-nat p q c) (Tˢ-natcont-isprop _ _)

-- Packaging it all up into a functor

Tᵒ : TSet → Time → TSet
Tᵒ A τ = tset (λ t → Tˢʳ A τ t) Tˢʳ-≤t Tˢʳ-≤t-refl Tˢʳ-≤t-trans

Tᶠ : ∀ {A B τ} → A →ᵗ B → Tᵒ A τ →ᵗ Tᵒ B τ
Tᶠ f = tset-map (Tˢʳᶠ f) (Tˢʳᶠ-nat f)


T-≤τ : ∀ {A τ τ'} → τ ≤ τ' → Tᵒ A τ →ᵗ Tᵒ A τ'
T-≤τ p = tset-map (Tˢʳ-≤τ p) (Tˢʳ-≤τ-t-nat p)

-- T is a [_]-module

T-[]-moduleˢ : ∀ {A τ τ' t} → Tˢ A τ' (t + τ) → Tˢ A (τ + τ') t
T-[]-moduleˢ {A} {τ} {τ'} {t} (leaf v) =
  leaf
    (monotone A
      (≤-reflexive
        (trans
          (trans
            (cong (τ' +_) (+-comm t τ))
            (sym (+-assoc τ' τ t)))
          (cong (_+ t) (+-comm τ' τ))))
      v)
T-[]-moduleˢ {A} {τ} {τ'} {t} (node {τ = τ''} op v k p) =
  node op v
    (λ {t'} q y →
      T-[]-moduleˢ
        (k (≤-trans
             (≤-reflexive
               (trans
                 (+-assoc t τ (op-time op))
                   (trans
                     (cong (t +_) (+-comm τ (op-time op)))
                       (sym (+-assoc t (op-time op) τ)))))
             (+-monoˡ-≤ τ q))
           y))
    (trans
      (cong (τ +_) p)
      (trans
        (sym (+-assoc τ (op-time op) τ''))
        (trans
          (cong (_+ τ'') (+-comm τ (op-time op)))
          (+-assoc (op-time op) τ _))))

T-[]-moduleˢ-t-nat : ∀ {A τ τ' t t'}
                   → (p : t ≤ t') → (c : Tˢ A τ' (t + τ))
                   → T-[]-moduleˢ (Tˢ-≤t (+-mono-≤ p (≤-reflexive refl)) c)
                   ≡ Tˢ-≤t p (T-[]-moduleˢ c)

T-[]-moduleˢ-t-nat {A} p (leaf v) =
  cong leaf
    (trans
      (monotone-trans A _ _ v)
      (trans
        (cong (λ r → monotone A r v) (≤-irrelevant _ _))
        (sym (monotone-trans A _ _ v))))
T-[]-moduleˢ-t-nat p (node op v k q) =
  cong₂ (node op v)
    (ifun-ext (fun-ext (λ r → fun-ext (λ y →
      cong (λ s → T-[]-moduleˢ (k s y)) (≤-irrelevant _ _)))))
    refl

T-[]-moduleˢ-natcont : ∀ {A τ τ' t} {c : Tˢ A τ' (t + τ)}
                      → Tˢ-natcont c
                      → Tˢ-natcont (T-[]-moduleˢ {A} {τ} {τ'} {t} c)
T-[]-moduleˢ-natcont natcont-leaf =
  natcont-leaf
T-[]-moduleˢ-natcont {A} {τ} {τ'} {t} {node {τ = τ''} op v k _} (natcont-node p q) =
  natcont-node
    (λ r s y →
      trans
      (cong T-[]-moduleˢ
        (trans
          (cong (λ p → k p y) (≤-irrelevant _ _))
          (p _ _ y)))
      (T-[]-moduleˢ-t-nat s _))
    (λ r  y →
      T-[]-moduleˢ-natcont
        (q
          (≤-trans
            (≤-reflexive
              (trans
                (+-assoc t τ (op-time op))
                (trans
                  (cong (t +_) (+-comm τ (op-time op)))
                  (sym (+-assoc t (op-time op) τ)))))
            (+-monoˡ-≤ _ r))
          y))

T-[]-moduleˢʳ : ∀ {A τ τ' t} → Tˢʳ A τ' (t + τ) → Tˢʳ A (τ + τ') t
T-[]-moduleˢʳ (c , p) = T-[]-moduleˢ c , T-[]-moduleˢ-natcont p

T-[]-moduleˢʳ-t-nat : ∀ {A τ τ' t t'}
                    → (p : t ≤ t') → (c : Tˢʳ A τ' (t + τ))
                    → T-[]-moduleˢʳ (Tˢʳ-≤t (+-mono-≤ p (≤-reflexive refl)) c)
                    ≡ Tˢʳ-≤t p (T-[]-moduleˢʳ c)
T-[]-moduleˢʳ-t-nat p (c , q) =
  dcong₂ _,_ (T-[]-moduleˢ-t-nat p c) (Tˢ-natcont-isprop _ _)

T-[]-module : ∀ {A τ τ'} → [ τ ]ᵒ (Tᵒ A τ') →ᵗ Tᵒ A (τ + τ')
T-[]-module = tset-map T-[]-moduleˢʳ T-[]-moduleˢʳ-t-nat

-- Unit

ηᵀ : ∀ {A} → A →ᵗ Tᵒ A 0
ηᵀ {A} =
  tset-map
    (λ v → leaf v , natcont-leaf)
    (λ p x →
      dcong₂ _,_
        (cong leaf
          (cong
            (λ q → monotone A q x)
            (≤-irrelevant _ _)))
        (Tˢ-natcont-isprop _ _))

-- Multiplication

μˢ : ∀ {A τ τ'} → {t : Time}
   → Tˢ (Tᵒ A τ') τ t → Tˢ A (τ + τ') t

μˢ {A} {τ} {τ'} {t} (leaf (c , p)) =
  T-[]-moduleˢ (Tˢ-≤t (≤-reflexive (+-comm τ t)) c)
μˢ (node op v k p) =
  node op v
    (λ q y → μˢ (k q y))
    (trans (cong (_+ _) p) (+-assoc (op-time op) _ _))

μˢ-t-nat : ∀ {A τ τ' t t'}
         → (p : t ≤ t')
         → (c : Tˢ (Tᵒ A τ') τ t)
         → μˢ (Tˢ-≤t p c) ≡ Tˢ-≤t p (μˢ c)
μˢ-t-nat p (leaf (c , q)) =
  trans
    (cong T-[]-moduleˢ
      (trans
        (Tˢ-≤t-trans _ _ c)
        (trans
          (cong (λ q → Tˢ-≤t q c) (≤-irrelevant _ _))
          (sym (Tˢ-≤t-trans _ _ c)))))
    (T-[]-moduleˢ-t-nat p _)
μˢ-t-nat p (node op v k q) = refl

μˢ-natcont : ∀ {A τ τ' t} {c : Tˢ (Tᵒ A τ') τ t}
           → Tˢ-natcont c
           → Tˢ-natcont (μˢ c)
μˢ-natcont {A} {τ} {τ'} {t} {leaf (c , p)} natcont-leaf =
  T-[]-moduleˢ-natcont (Tˢ-≤t-natcont (≤-reflexive (+-comm τ t)) p)
μˢ-natcont {A} {τ} {τ'} {t} {node op v k _} (natcont-node p q) =
  natcont-node
    (λ r s y →
      trans
        (cong μˢ (p r s y))
        (μˢ-t-nat s (k r y)))
    (λ r y → μˢ-natcont (q r y))

μˢʳ : ∀ {A τ τ'} → {t : Time}
    → carrier (Tᵒ (Tᵒ A τ') τ) t → carrier (Tᵒ A (τ + τ')) t
μˢʳ (c , p) = μˢ c , μˢ-natcont p

μˢʳ-t-nat : ∀ {A τ τ' t t'}
          → (p : t ≤ t')
          → (c : carrier (Tᵒ (Tᵒ A τ') τ) t)
          → μˢʳ (Tˢʳ-≤t p c) ≡ Tˢʳ-≤t p (μˢʳ c)
μˢʳ-t-nat p (c , q) =
  dcong₂ _,_ (μˢ-t-nat p c) (Tˢ-natcont-isprop _ _)

μᵀ : ∀ {A τ τ'} → Tᵒ (Tᵒ A τ') τ →ᵗ Tᵒ A (τ + τ')
μᵀ = tset-map μˢʳ μˢʳ-t-nat


-- Strength

strˢ : ∀ {A B τ τ' t}
     → carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t
     → Tˢ B τ t
     → Tˢ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ t
     
strˢ {A} {B} {τ} {τ'} {t} (vp , vx) (leaf w) =
  leaf (
    (≤-trans vp (≤-reflexive (+-comm t τ)) ,
     monotone A (≤-reflexive (cong (_∸ τ') (+-comm t τ))) vx) ,
    w)
strˢ {A} {B} {τ' = τ''} {t} (vp , vx) (node {τ = τ} {τ' = τ'} op w k p) =
  node op w
    (λ q y →
      strˢ {A = A} {B = B} {τ = τ} {τ' = τ''}
        (≤-trans
           (≤-trans
             vp
             (≤-trans
               (≤-reflexive (cong (t +_) p))
               (≤-reflexive (sym (+-assoc t (op-time op) τ)))))
           (+-monoˡ-≤ τ q) ,
         monotone A
           (≤-trans
             (≤-reflexive (cong (λ τ' → t + τ' ∸ τ'') p))
             (≤-trans
               (≤-reflexive (cong (_∸ τ'') (sym (+-assoc t (op-time op) τ))))
               (∸-monoˡ-≤ τ'' (+-monoˡ-≤ τ q))))
           vx)
        (k q y))
    p

strˢ-t-nat : ∀ {A B τ τ'} → {t t' : ℕ} → (p : t ≤ t')
           → (x : carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t × Tˢ B τ t)
           → strˢ {A = A} {B = B}
               (monotone ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) p (proj₁ x))
               (Tˢ-≤t p (proj₂ x))
           ≡ Tˢ-≤t p (strˢ {A = A} {B = B} (proj₁ x) (proj₂ x))

strˢ-t-nat {A} p (x , leaf v) =
  cong leaf
    (cong₂ _,_
      (cong₂ _,_
        (≤-irrelevant _ _)
        (trans
          (monotone-trans A _ _ (proj₂ x))
          (trans
            (cong (λ q → monotone A q (proj₂ x)) (≤-irrelevant _ _))
            (sym (monotone-trans A _ _ (proj₂ x))))))
      refl)
strˢ-t-nat {A} p (x , node op v k q) =
  cong₂ (node op v)
    (ifun-ext (fun-ext (λ r → fun-ext (λ y →
      cong₂ strˢ
        (cong₂ _,_
          (≤-irrelevant _ _)
          (trans
            (monotone-trans A _ _ (proj₂ x))
            (cong (λ s → monotone A s (proj₂ x)) (≤-irrelevant _ _))))
        refl))))
    refl

strˢʳ-natcont : ∀ {A B τ τ' t}
              → {x : carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t}
              → {c : Tˢ B τ t}
              → (p : Tˢ-natcont c)
              → Tˢ-natcont (strˢ {A} {B} {τ} {τ'} {t} x c)
strˢʳ-natcont natcont-leaf = natcont-leaf
strˢʳ-natcont {A} {B} {τ} {τ'} {t} {x} (natcont-node p q) =
  natcont-node
    (λ r s y →
      trans
        (cong₂ strˢ
          (cong₂ _,_
            (≤-irrelevant _ _)
            (trans
              (cong (λ p → monotone A p (proj₂ x)) (≤-irrelevant _ _))
              (sym (monotone-trans A _ _ (proj₂ x)))))
          (p r s y))
        (strˢ-t-nat _ _))
    (λ r y → strˢʳ-natcont (q r y))

strˢʳ : ∀ {A B τ τ' t}
      → carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A)) t × carrier (Tᵒ B τ) t
      → carrier (Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ) t
strˢʳ {A} {B} {τ} {τ'} {t} (x , (c , p)) =
  strˢ {A} {B} {τ} {τ'} {t} x c , strˢʳ-natcont p

strˢʳ-t-nat : ∀ {A B τ τ' t t'} → (p : t ≤ t')
            → (xc : carrier ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ) t)
            → strˢʳ {A} {B} {τ} {τ'}
                (monotone ([ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ) p xc)
            ≡ monotone (Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ) p (strˢʳ {A} {B} {τ} {τ'} xc)
strˢʳ-t-nat p (x , (c , q)) =
  dcong₂ _,_ (strˢ-t-nat p (x , c)) (Tˢ-natcont-isprop _ _)

strᵀ : ∀ {A B τ τ'} → [ τ ]ᵒ (⟨ τ' ⟩ᵒ A) ×ᵗ Tᵒ B τ →ᵗ Tᵒ (⟨ τ' ⟩ᵒ A ×ᵗ B) τ
strᵀ {A} {B} {τ} {τ'} =
  tset-map (strˢʳ {A} {B} {τ} {τ'}) strˢʳ-t-nat

-- Algebraic operations

opᵀ : ∀ {A τ} → (op : Op)
    → ConstTSet ⟦ param op ⟧ᵍ
    ×ᵗ [ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ A τ)
    →ᵗ Tᵒ A (op-time op + τ)
   
opᵀ {A} {τ} op =
  tset-map
    (λ { (v , k) →
      node op v
        (λ p y → proj₁ (map-carrier k (p , y))) refl ,
      natcont-node
        (λ p q y → cong proj₁ (map-nat k q (p , y)))
        (λ p y → proj₂ (map-carrier k (p , y))) })
    (λ { p (v , k) →
      dcong₂ _,_ refl (Tˢ-natcont-isprop _ _) })


-- Semantics of effect handling (every effect
-- handler induces a corresponding monad algebra)

handler-to-algˢ : ∀ {A τ τ' t}
                → ((op : Op) → (τ'' : Time) → {t' : Time} → t ≤ t' → 
                    carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
                    ({t'' : Time} → t' + op-time op ≤ t'' →
                      carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ A τ'') t'') →
                    carrier (Tᵒ A (op-time op + τ'')) t')
                → Tˢ (Tᵒ A τ') τ t
                → carrier (Tᵒ A (τ + τ')) t

handler-to-algˢ {τ = τ} {t = t} h (leaf (c , p)) =
  T-[]-moduleˢ (Tˢ-≤t (≤-reflexive (+-comm τ t)) c) ,
  T-[]-moduleˢ-natcont (Tˢ-≤t-natcont (≤-reflexive (+-comm τ t)) p)
handler-to-algˢ {A} {τ' = τ'} {t = t} h (node {τ = τ''} op v k p) =
  Tˢʳ-≤τ
    (≤-reflexive
      (trans
        (sym (+-assoc (op-time op) τ'' τ'))
        (cong (_+ τ') (sym p))))
    (h op (τ'' + τ') ≤-refl v
      (λ q y →
        handler-to-algˢ
          (λ op τ''' r x k' → h op τ''' (≤-trans (m+n≤o⇒m≤o t q) r) x k')
          (k q y)))

handler-to-algˢʳ : ∀ {A τ τ' t}
                 → ((op : Op) → (τ'' : Time) → {t' : Time} → t ≤ t' → 
                     carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
                     ({t'' : Time} → t' + op-time op ≤ t'' →
                       carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ A τ'') t'') →
                     carrier (Tᵒ A (op-time op + τ'')) t')
                 → carrier (Tᵒ (Tᵒ A τ') τ) t
                 → carrier (Tᵒ A (τ + τ')) t

handler-to-algˢʳ h (c , p) = handler-to-algˢ h c

handler-to-algˢʳ-t-nat : ∀ {A τ τ' t t'}
                       → (p : t ≤ t')
                       → (h : (op : Op) → (τ'' : Time) → {t' : Time} → t ≤ t' → 
                           carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
                           ({t'' : Time} → t' + op-time op ≤ t'' →
                             carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ A τ'') t'') →
                           carrier (Tᵒ A (op-time op + τ'')) t')
                       → (h-nat : (op : Op) → (τ'' : Time)
                                → {t' : Time} → (p : t ≤ t')
                                → {t'' : Time} → (q : t' ≤ t'')
                                → (x : carrier (ConstTSet ⟦ param op ⟧ᵍ) t')
                                → (k : {t'' : Time} → t' + op-time op ≤ t'' →
                                         carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ A τ'') t'')
                                → h op τ'' (≤-trans p q) x (λ r y → Tˢʳ-≤t r (k (+-monoˡ-≤ (op-time op) q) y))
                                ≡ Tˢʳ-≤t q (h op τ'' p x k))
                       → (c : carrier (Tᵒ (Tᵒ A τ') τ) t)
                       → handler-to-algˢ (λ op τ'' q x k → h op τ'' (≤-trans p q) x k) (Tˢ-≤t p (proj₁ c))
                       ≡ Tˢʳ-≤t p (handler-to-algˢʳ h c)

handler-to-algˢʳ-t-nat p h h-nat (leaf (c , q) , r) =
  trans
    (cong T-[]-moduleˢʳ
      (trans
        (Tˢʳ-≤t-trans _ _ _)
        (trans
          (cong
            (λ s → Tˢʳ-≤t s (c , q))
            (≤-irrelevant _ _))
          (sym (Tˢʳ-≤t-trans _ _ _)))))
    (T-[]-moduleˢʳ-t-nat _ _)
handler-to-algˢʳ-t-nat {A} {τ} {τ'} {t} {t'} p h h-nat (node {τ = τ''} op v k q , natcont-node s s') =
  trans
    (cong
      (Tˢʳ-≤τ (≤-reflexive
        (trans (sym (+-assoc (op-time op) τ'' τ')) (cong (_+ τ') (sym q)))))
      (trans
        (trans
          (trans
            ((cong (λ s → (h op (τ'' + τ') s v
               (λ q₁ y → handler-to-algˢ (λ op₁ τ''' r →
                 h op₁ τ''' (≤-trans p (≤-trans (m+n≤o⇒m≤o t' q₁) r)))
                   (k (≤-trans (+-monoˡ-≤ (op-time op) p) q₁) y))))
               (≤-irrelevant _ p)))
            (cong (h op (τ'' + τ') p v)
              (ifun-ext (fun-ext (λ r → fun-ext (λ y →
                trans
                  (cong₂ handler-to-algˢ
                    (fun-ext (λ op → fun-ext (λ τ''' → ifun-ext (fun-ext (λ r' →
                      cong (h op τ''') (≤-irrelevant _ _))))))
                    (s _ _ _))
                  (handler-to-algˢʳ-t-nat r
                    (λ op₁ τ''' r₁ →
                      h op₁ τ''' (≤-trans (m+n≤o⇒m≤o t (+-monoˡ-≤ (op-time op) p)) r₁))
                    (λ op τ''' r' r'' x' k' →
                      trans
                        (cong (λ r'' → h op τ''' r'' x' _) (≤-irrelevant _ _))
                        (h-nat op τ''' _ _ _ _))
                    (k (+-monoˡ-≤ (op-time op) p) y , s' _ y))))))))
          (cong
            (λ s → h op (τ'' + τ') s v
              (λ r y → Tˢʳ-≤t r (handler-to-algˢ (λ op₁ τ''' r₁ →
                h op₁ τ''' (≤-trans (m+n≤o⇒m≤o t (+-monoˡ-≤ (op-time op) p)) r₁))
                 (k (+-monoˡ-≤ (op-time op) p) y))))
            (≤-irrelevant p _)))
        (h-nat op (τ'' + τ') _ _ _ _)))
    (Tˢʳ-≤τ-t-nat _ _ _)

handler-to-alg : ∀ {A τ τ'}
               → Π Op (λ op → Π Time (λ τ'' →
                  ConstTSet ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ A τ'')))
                    ⇒ᵗ Tᵒ A (op-time op + τ'')))
              ×ᵗ Tᵒ (Tᵒ A τ') τ 
              →ᵗ (Tᵒ A (τ + τ'))
              
handler-to-alg =
  tset-map
    (λ { (h , c) →
      handler-to-algˢʳ
        (λ op τ'' p x k →
          map-carrier (h op τ'')
            (p , x ,
             tset-map
               (λ { (q , y) → Tˢʳ-≤t q (k ≤-refl y) })
               (λ { q (r , y) → sym (Tˢʳ-≤t-trans _ _ _) })))
        c })
    (λ { p (h , c) → {!!} })






















-- TODO: figure out the right recursion pattern

-- Semantics of effect handling (the mediating
-- homomorphism induced by a given algebra)
{-
handleˢ : ∀ {A B τ τ' t}
        → Tˢ A τ t
        → ((op : Op) → (τ'' : Time) →
             {t' : Time} → t ≤ t' → 
             carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
             ({t'' : Time} → t' + op-time op ≤ t'' →
                carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ B τ'') t'') →
             carrier (Tᵒ B (op-time op + τ'')) t')
        → ({t' : Time} → t + τ ≤ t' → carrier A t' → carrier (Tᵒ B τ') t')
        → carrier (Tᵒ B (τ + τ')) t

handleˢ {τ = τ} {t = t} (leaf v) h k =
  T-[]-moduleˢʳ
    (Tˢʳ-≤t
      (≤-reflexive (+-comm τ t))
      (k (≤-reflexive (+-comm t τ)) v))
handleˢ {τ' = τ'} {t = t} (node {τ = τ''} op v k p) h k' =
  Tˢʳ-≤τ
    (≤-reflexive
      (trans
        (sym (+-assoc (op-time op) τ'' τ'))
        (cong (_+ τ') (sym p))))
    (h op (τ'' + τ') ≤-refl v
      (λ q y →
        handleˢ
          (k q y)
            (λ op τ''' r x k'' →
              h op τ''' (≤-trans (m+n≤o⇒m≤o t q) r) x k'')
            (λ r z → k'
              (≤-trans
                (≤-reflexive (cong (t +_) p))
                (≤-trans
                  (≤-trans
                    (≤-reflexive (sym (+-assoc t (op-time op) τ'')))
                    (+-monoˡ-≤ τ'' q))
                  r)) z)))

handleˢ-t-nat : ∀ {A B τ τ' t t'}
              → (p : t ≤ t')
              → (c : Tˢ A τ t)
              → (h : (op : Op) → (τ'' : Time) →
                       {t' : Time} → t ≤ t' → 
                       carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
                       ({t'' : Time} → t' + op-time op ≤ t'' →
                         carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ B τ'') t'') →
                       carrier (Tᵒ B (op-time op + τ'')) t')
              → (k : carrier ([ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')) t)
              → handleˢ
                  (Tˢ-≤t p c)
                  (λ op τ'' q x k' → h op τ'' (≤-trans p q) x k')
                  (λ q z → map-carrier k (≤-trans (+-monoˡ-≤ τ p) q , z))
              ≡ Tˢʳ-≤t p (handleˢ c h (λ q z → map-carrier k (q , z)))

handleˢ-t-nat {A} {B} {τ} {τ'} {t} {t'} p (leaf v) h k =
  trans
    (cong T-[]-moduleˢʳ
      (trans
        (sym (map-nat k _ _))
        (trans
          (trans
            (cong (map-carrier k)
              (cong₂ _,_
                (≤-irrelevant _ _)
                (trans
                  (monotone-trans A _ _ _)
                  (cong
                    (λ p → monotone A p v)
                    (≤-irrelevant _ _)))))
            (map-nat k _ _))
          (sym (monotone-trans (Tᵒ B τ') _ _ _)))))
    (T-[]-moduleˢʳ-t-nat _ _)
handleˢ-t-nat p (node op v k q) h k' =
  {!!}
-}

{-

handleˢʳ : ∀ {A B τ τ' t}
         → carrier (Tᵒ A τ) t
         → ((op : Op) → (τ'' : Time) →
              {t' : Time} → t ≤ t' → 
              carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
              ({t'' : Time} → t' + op-time op ≤ t'' →
                 carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ B τ'') t'') →
              carrier (Tᵒ B (op-time op + τ'')) t')
         → ({t' : Time} → t + τ ≤ t' → carrier A t' → carrier (Tᵒ B τ') t')
         → carrier (Tᵒ B (τ + τ')) t

handleˢʳ (c , p) h k = handleˢ c h k
-}

{-
handleᵀ : ∀ {A B τ τ'}
        → Tᵒ A τ
        ×ᵗ Π Op (λ op → Π Time (λ τ'' →
            ConstTSet ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ B τ'')))
              ⇒ᵗ Tᵒ B (op-time op + τ'')))
        ×ᵗ [ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')
        →ᵗ Tᵒ B (τ + τ')

handleᵀ {A} {B} {τ} {τ'} =
  let handle-map : {t : Time}
                 → carrier (
                     Tᵒ A τ ×ᵗ
                     Π Op (λ op → Π Time (λ τ'' →
                       ConstTSet ⟦ param op ⟧ᵍ ×ᵗ
                       [ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ B τ'')
                         ⇒ᵗ Tᵒ B (op-time op + τ''))) ×ᵗ
                     [ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')) t
                 → carrier (Tᵒ B (τ + τ')) t
      handle-map =
        λ { (c , h , k) →
          handleˢʳ
            c
            (λ op τ'' p x k' →
              map-carrier (h op τ'') (p , x , tset-map (λ { (q , y) → k' q y }) {!!}))
            {!!} } in
  tset-map
    handle-map
    {!!}
-}

{-
      handle-map =
        λ { (c , h , k) →
          handleˢ c
            (λ op τ'' p x k' →
              map-carrier (h op τ'')
                (p , x ,
                 tset-map
                   (λ { (q , y) → Tˢ-≤t q (k' ≤-refl y) })
                   (λ { q (r , y) → sym (Tˢ-≤t-trans _ _ _) })))
            (λ p x → map-carrier k (p , x)) } in
-}


{-
-- Semantics of effect handling (the mediating
-- homomorphism induced by a given algebra)

handleˢ : ∀ {A B τ τ' t}
        → carrier (Tᵒ A τ) t
        → ((op : Op) → (τ'' : Time) →
             {t' : Time} → t ≤ t' → 
             carrier (ConstTSet ⟦ param op ⟧ᵍ) t' →
             ({t'' : Time} → t' + op-time op ≤ t'' →
                carrier (ConstTSet ⟦ arity op ⟧ᵍ) t'' → carrier (Tᵒ B τ'') t'') →
             carrier (Tᵒ B (op-time op + τ'')) t')
        → ({t' : Time} → t + τ ≤ t' → carrier A t' → carrier (Tᵒ B τ') t')
        → carrier (Tᵒ B (τ + τ')) t
        
handleˢ {τ = τ} {t = t} (leaf v) h k =
  T-[]-moduleˢ
    (Tˢ-≤t
      (≤-reflexive (+-comm τ t))
      (k (≤-reflexive (+-comm t τ)) v))
handleˢ {τ' = τ'} {t = t} (node {τ = τ''} op v k refl) h k' =
  Tˢ-≤τ
    (≤-reflexive (sym (+-assoc (op-time op) τ'' τ')))
    (h op (τ'' + τ') ≤-refl v
      (λ q y →
        handleˢ
          (k q y)
          (λ op τ''' r x k'' →
            h op τ'''
              (≤-trans (m+n≤o⇒m≤o t q) r)
              x
              k'')
          (λ r z →
            k' (≤-trans
                 (≤-trans
                   (≤-reflexive (sym (+-assoc t (op-time op) τ'')))
                   (+-monoˡ-≤ τ'' q)) r) z)))

handleᵀ : ∀ {A B τ τ'}
        → Tᵒ A τ
        ×ᵗ Π Op (λ op → Π Time (λ τ'' →
            ConstTSet ⟦ param op ⟧ᵍ ×ᵗ ([ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ (Tᵒ B τ'')))
              ⇒ᵗ Tᵒ B (op-time op + τ'')))
        ×ᵗ [ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')
        →ᵗ Tᵒ B (τ + τ')

handleᵀ {A} {B} {τ} {τ'} =
  let handle-map : {t : Time}
                 → carrier (
                     Tᵒ A τ ×ᵗ
                     Π Op (λ op → Π Time (λ τ'' →
                       ConstTSet ⟦ param op ⟧ᵍ ×ᵗ
                       [ op-time op ]ᵒ (ConstTSet ⟦ arity op ⟧ᵍ ⇒ᵗ Tᵒ B τ'')
                         ⇒ᵗ Tᵒ B (op-time op + τ''))) ×ᵗ
                     [ τ ]ᵒ (A ⇒ᵗ Tᵒ B τ')) t
                 → carrier (Tᵒ B (τ + τ')) t
      handle-map =
        λ { (c , h , k) →
          handleˢ c
            (λ op τ'' p x k' →
              map-carrier (h op τ'')
                (p , x ,
                 tset-map
                   (λ { (q , y) → Tˢ-≤t q (k' ≤-refl y) })
                   (λ { q (r , y) → sym (Tˢ-≤t-trans _ _ _) })))
            (λ p x → map-carrier k (p , x)) } in
  tset-map handle-map {!!}
    
{-
  tset-map
    (λ { (c , h , k) →
      handleˢ c (λ op τ'' p x k' →
        h op τ'' p (x , λ q y → k' q y)) k })
    ?
-}


-}
