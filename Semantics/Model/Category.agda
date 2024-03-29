-------------------------------------------------------
-- Category structure for the models of the language --
-------------------------------------------------------

module Semantics.Model.Category where

open import Util.Equality

record Category : Set₂ where

  -- OBJECTS AND MORPHISMS
  
  field
    Obj : Set₁
    
    _→ᵐ_ : (A B : Obj) → Set₀

  infix 20 _→ᵐ_

  -- IDENTITIES AND COMPOSITION
  
  field
    idᵐ : ∀ {A} → A →ᵐ A
    _∘ᵐ_ : ∀ {A B C} → B →ᵐ C → A →ᵐ B → A →ᵐ C

    ∘ᵐ-identityˡ : ∀ {A B} → (f : A →ᵐ B) → idᵐ ∘ᵐ f ≡ f
    ∘ᵐ-identityʳ : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ idᵐ ≡ f   
    ∘ᵐ-assoc : ∀ {A B C D} → (h : C →ᵐ D) → (g : B →ᵐ C) → (f : A →ᵐ B) → (h ∘ᵐ g) ∘ᵐ f ≡ h ∘ᵐ (g ∘ᵐ f)
    
  infixr 9 _∘ᵐ_

  -- TERMINAL OBJECT

  field
    𝟙ᵐ : Obj

    terminalᵐ : ∀ {A} → A →ᵐ 𝟙ᵐ
    terminalᵐ-unique : ∀ {A} {f : A →ᵐ 𝟙ᵐ} → f ≡ terminalᵐ

  -- INITIAL OBJECT
  
  field
    𝟘ᵐ : Obj

    initialᵐ : ∀ {A} → 𝟘ᵐ →ᵐ A
    initialᵐ-unique : ∀ {A} {f : 𝟘ᵐ →ᵐ A} → f ≡ initialᵐ

  -- BINARY PRODUCTS (should be derived from set-indexed products below)

  field
    _×ᵐ_ : Obj → Obj → Obj

    fstᵐ : ∀ {A B} → A ×ᵐ B →ᵐ A
    sndᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B
    ⟨_,_⟩ᵐ : ∀ {A B C} → A →ᵐ B → A →ᵐ C → A →ᵐ B ×ᵐ C

    ⟨⟩ᵐ-fstᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → fstᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ f
    ⟨⟩ᵐ-sndᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → sndᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ g
    ⟨⟩ᵐ-unique : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → (h : A →ᵐ B ×ᵐ C) → fstᵐ ∘ᵐ h ≡ f → sndᵐ ∘ᵐ h ≡ g → h ≡ ⟨ f , g ⟩ᵐ

  mapˣᵐ : ∀ {A B C D} → A →ᵐ C → B →ᵐ D → A ×ᵐ B →ᵐ C ×ᵐ D
  mapˣᵐ f g = ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
  
  infixr 23 _×ᵐ_

  -- SET-INDEXED PRODUCTS

  field
    Πᵐ : (I : Set) → (I → Obj) → Obj
    
    projᵐ : ∀ {I A} → (i : I) → Πᵐ I A →ᵐ A i
    ⟨_⟩ᵢᵐ : ∀ {I A B} → ((i : I) → A →ᵐ B i) → A →ᵐ Πᵐ I B

    ⟨⟩ᵢᵐ-projᵐ : ∀ {I} {A} {B : I → Obj} → (f : ((i : I) → A →ᵐ B i)) → (i : I) → projᵐ i ∘ᵐ ⟨ f ⟩ᵢᵐ ≡ f i
    ⟨⟩ᵢᵐ-unique : ∀ {I} {A} {B : I → Obj}
                → (f : (i : I) → A →ᵐ B i)
                → (g : A →ᵐ Πᵐ I B)
                → ((i : I) → (projᵐ i ∘ᵐ g) ≡ f i)
                → g ≡ ⟨ f ⟩ᵢᵐ

  -- EXPONENTIALS

  field
    _⇒ᵐ_ : Obj → Obj → Obj

    curryᵐ : ∀ {A B C} → A ×ᵐ B →ᵐ C → A →ᵐ B ⇒ᵐ C
    curryᵐ-nat : ∀ {A B C D} → (f : A →ᵐ B) → (g : B ×ᵐ C →ᵐ D)
               → curryᵐ (g ∘ᵐ mapˣᵐ f idᵐ) ≡ curryᵐ g ∘ᵐ f

    uncurryᵐ : ∀ {A B C} → A →ᵐ B ⇒ᵐ C → A ×ᵐ B →ᵐ C
    uncurryᵐ-nat : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C ⇒ᵐ D)
                 → uncurryᵐ (g ∘ᵐ f) ≡ uncurryᵐ g ∘ᵐ mapˣᵐ f idᵐ

    curryᵐ-uncurryᵐ-iso : ∀ {A B C} → (f : A ×ᵐ B →ᵐ C)
                        → uncurryᵐ (curryᵐ f) ≡ f
    uncurryᵐ-curryᵐ-iso : ∀ {A B C} → (f : A →ᵐ B ⇒ᵐ C)
                        → curryᵐ (uncurryᵐ f) ≡ f

  infixr 22 _⇒ᵐ_
