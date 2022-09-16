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

  -- EQUALITY ON MORPHISMS

  field
    _≡ᵐ_ : {A B : Obj} (f g : A →ᵐ B) → Set

    ≡ᵐ-refl : ∀ {A B} {f : A →ᵐ B} → f ≡ᵐ f
    ≡ᵐ-sym : ∀ {A B} {f g : A →ᵐ B} → f ≡ᵐ g → g ≡ᵐ f
    ≡ᵐ-trans : ∀ {A B} {f g h : A →ᵐ B} → f ≡ᵐ g → g ≡ᵐ h → f ≡ᵐ h

    begin_ : ∀ {A B} {f g : A →ᵐ B} → f ≡ᵐ g → f ≡ᵐ g
     
    _≡⟨⟩_ : ∀ {A B} (f {g} : A →ᵐ B) → f ≡ᵐ g → f ≡ᵐ g
     
    step-≡ : ∀ {A B} (f {g h} : A →ᵐ B) → g ≡ᵐ h → f ≡ᵐ g → f ≡ᵐ h
     
    _∎ : ∀ {A B} (f : A →ᵐ B) → f ≡ᵐ f

    ≡ᵐ-≡ : ∀ {A B} → {f g : A →ᵐ B} → f ≡ᵐ g → f ≡ g
    ≡-≡ᵐ : ∀ {A B} → {f g : A →ᵐ B} → f ≡ g → f ≡ᵐ g

    ≡ᵐ-cong : ∀ {A B C D} (f : (A →ᵐ B) → (C →ᵐ D)) {x y : A →ᵐ B}
            → x ≡ᵐ y → f x ≡ᵐ f y
    ≡ᵐ-cong₂ : ∀ {A B C D E F} (f : (A →ᵐ B) → (C →ᵐ D) → (E →ᵐ F))
             → {x y : A →ᵐ B} {z w : C →ᵐ D}
             → x ≡ᵐ y → z ≡ᵐ w → f x z ≡ᵐ f y w

  infix  5 _≡ᵐ_
  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡
  infix  1 begin_

  syntax step-≡ f g≡h f≡g = f ≡⟨ f≡g ⟩ g≡h

  -- iDENTITIES AND COMPOSITION
  
  field
    idᵐ : ∀ {A} → A →ᵐ A
    _∘ᵐ_ : ∀ {A B C} → B →ᵐ C → A →ᵐ B → A →ᵐ C

    ∘ᵐ-identityˡ : ∀ {A B} → (f : A →ᵐ B) → idᵐ ∘ᵐ f ≡ᵐ f
    ∘ᵐ-identityʳ : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ idᵐ ≡ᵐ f   
    ∘ᵐ-assoc : ∀ {A B C D} → (h : C →ᵐ D) → (g : B →ᵐ C) → (f : A →ᵐ B) → (h ∘ᵐ g) ∘ᵐ f ≡ᵐ h ∘ᵐ (g ∘ᵐ f)
    ∘ᵐ-congˡ : ∀ {A B C} → {f : A →ᵐ B} → {g h : B →ᵐ C} → g ≡ᵐ h → g ∘ᵐ f ≡ᵐ h ∘ᵐ f
    ∘ᵐ-congʳ : ∀ {A B C} → {f g : A →ᵐ B} → {h : B →ᵐ C} → f ≡ᵐ g → h ∘ᵐ f ≡ᵐ h ∘ᵐ g

  infixr 9 _∘ᵐ_

  -- TERMINAL OBJECT

  field
    𝟙ᵐ : Obj

    terminalᵐ : ∀ {A} → A →ᵐ 𝟙ᵐ
    terminalᵐ-unique : ∀ {A} {f : A →ᵐ 𝟙ᵐ} → f ≡ᵐ terminalᵐ

  -- INITIAL OBJECT
  
  field
    𝟘ᵐ : Obj

    initialᵐ : ∀ {A} → 𝟘ᵐ →ᵐ A
    initialᵐ-unique : ∀ {A} {f : 𝟘ᵐ →ᵐ A} → f ≡ᵐ initialᵐ

  -- BINARY PRODUCTS

  field
    _×ᵐ_ : Obj → Obj → Obj

    fstᵐ : ∀ {A B} → A ×ᵐ B →ᵐ A
    sndᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B
    ⟨_,_⟩ᵐ : ∀ {A B C} → A →ᵐ B → A →ᵐ C → A →ᵐ B ×ᵐ C

    ⟨⟩ᵐ-fstᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → fstᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ᵐ f
    ⟨⟩ᵐ-sndᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → sndᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≡ᵐ g
    ⟨⟩ᵐ-unique : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → (h : A →ᵐ B ×ᵐ C) → fstᵐ ∘ᵐ h ≡ᵐ f → sndᵐ ∘ᵐ h ≡ᵐ g → h ≡ᵐ ⟨ f , g ⟩ᵐ

  mapˣᵐ : ∀ {A B C D} → A →ᵐ C → B →ᵐ D → A ×ᵐ B →ᵐ C ×ᵐ D
  mapˣᵐ f g = ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
   
  ×ᵐ-assoc : ∀ {A B C} → A ×ᵐ (B ×ᵐ C) →ᵐ (A ×ᵐ B) ×ᵐ C
  ×ᵐ-assoc = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
   
  ×ᵐ-assoc⁻¹ : ∀ {A B C} → (A ×ᵐ B) ×ᵐ C →ᵐ A ×ᵐ (B ×ᵐ C)
  ×ᵐ-assoc⁻¹ = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
   
  ×ᵐ-swap : ∀ {A B} → A ×ᵐ B →ᵐ B ×ᵐ A
  ×ᵐ-swap = ⟨ sndᵐ , fstᵐ ⟩ᵐ

  infixr 23 _×ᵐ_

  -- SET-INDEXED PRODUCTS

  field
    Π : (I : Set) → (I → Obj) → Obj
    
    projᵐ : ∀ {I A} → (i : I) → Π I A →ᵐ A i
    ⟨_⟩ᵢᵐ : ∀ {I A B} → ((i : I) → A →ᵐ B i) → A →ᵐ Π I B

  mapⁱˣᵐ : ∀ {I A B} → ((i : I) → A i →ᵐ B i) → Π I A →ᵐ Π I B
  mapⁱˣᵐ fs = ⟨ (λ i → fs i ∘ᵐ projᵐ i) ⟩ᵢᵐ

  field
    mapⁱˣᵐ-identity : ∀ {I A} → mapⁱˣᵐ {I} {A} {A} (λ i → idᵐ) ≡ᵐ idᵐ
    mapⁱˣᵐ-∘ᵐ : ∀ {I} {A B C : I → Obj} → (f : ((i : I) → A i →ᵐ B i)) → (g : ((i : I) → B i →ᵐ C i))
              → mapⁱˣᵐ (λ i → g i ∘ᵐ f i) ≡ᵐ mapⁱˣᵐ g ∘ᵐ mapⁱˣᵐ f

    ⟨⟩ᵢᵐ-projᵐ : ∀ {I} {A} {B : I → Obj} → (f : ((i : I) → A →ᵐ B i)) → (i : I) → projᵐ i ∘ᵐ ⟨ f ⟩ᵢᵐ ≡ᵐ f i
    ⟨⟩ᵢᵐ-∘ᵐ : ∀ {I} {A B} {C : I → Obj} → (f : A →ᵐ B) → (g : ((i : I) → B →ᵐ C i)) → ⟨ (λ i → g i ∘ᵐ f) ⟩ᵢᵐ ≡ᵐ ⟨ g ⟩ᵢᵐ ∘ᵐ f

  -- EXPONENTIALS

  field
    _⇒ᵐ_ : Obj → Obj → Obj

    appᵐ : ∀ {A B} → (A ⇒ᵐ B) ×ᵐ A →ᵐ B
    map⇒ᵐ : ∀ {A B C D} → (A →ᵐ B) → (C →ᵐ D) → B ⇒ᵐ C →ᵐ A ⇒ᵐ D
    curryᵐ : ∀ {A B C} → A ×ᵐ B →ᵐ C → A →ᵐ B ⇒ᵐ C
    uncurryᵐ : ∀ {A B C} → A →ᵐ B ⇒ᵐ C → A ×ᵐ B →ᵐ C

    map⇒ᵐ-identity : ∀ {A B} → map⇒ᵐ {A} {A} {B} {B} idᵐ idᵐ ≡ᵐ idᵐ
    
    curryᵐ-mapˣᵐ : ∀ {A B C D E} → (f : C ×ᵐ D →ᵐ E) → (g : A →ᵐ C) → (h : B →ᵐ D)
                 → curryᵐ (f ∘ᵐ mapˣᵐ g h) ≡ᵐ map⇒ᵐ h idᵐ ∘ᵐ curryᵐ f ∘ᵐ g
    uncurryᵐ-mapʳ : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C ⇒ᵐ D) → uncurryᵐ (g ∘ᵐ f) ≡ᵐ uncurryᵐ g ∘ᵐ mapˣᵐ f idᵐ

  infixr 22 _⇒ᵐ_
