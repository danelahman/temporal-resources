-------------------------------------------------------
-- Category structure for the models of the language --
-------------------------------------------------------

open import Semantics.Model.Category

module Semantics.Model.Category.Derived (Cat : Category) where

open import Util.Equality

open Category Cat

-- CONGRUENCE OF MORPHISM COMPOSITION

∘ᵐ-congˡ : ∀ {A B C} → {f : A →ᵐ B} → {g h : B →ᵐ C} → g ≡ h → g ∘ᵐ f ≡ h ∘ᵐ f
∘ᵐ-congˡ {f = f} p =
  cong (_∘ᵐ f) p

∘ᵐ-congʳ : ∀ {A B C} → {f g : A →ᵐ B} → {h : B →ᵐ C} → f ≡ g → h ∘ᵐ f ≡ h ∘ᵐ g
∘ᵐ-congʳ {h = h} p =
  cong (h ∘ᵐ_) p

-- BINARY PRODUCTS

×ᵐ-assoc : ∀ {A B C} → (A ×ᵐ B) ×ᵐ C →ᵐ A ×ᵐ (B ×ᵐ C)
×ᵐ-assoc = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

×ᵐ-assoc⁻¹ : ∀ {A B C} → A ×ᵐ (B ×ᵐ C) →ᵐ (A ×ᵐ B) ×ᵐ C
×ᵐ-assoc⁻¹ = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ

⟨⟩ᵐ-∘ᵐ : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C) → (h : B →ᵐ D)
       → ⟨ g ∘ᵐ f , h ∘ᵐ f ⟩ᵐ ≡ ⟨ g , h ⟩ᵐ ∘ᵐ f
⟨⟩ᵐ-∘ᵐ f g h = 
  begin
    ⟨ g ∘ᵐ f , h ∘ᵐ f ⟩ᵐ
  ≡⟨ sym
       (⟨⟩ᵐ-unique
         (g ∘ᵐ f) (h ∘ᵐ f) (⟨ g , h ⟩ᵐ ∘ᵐ f)
         (begin
            fstᵐ ∘ᵐ ⟨ g , h ⟩ᵐ ∘ᵐ f
          ≡⟨ sym (∘ᵐ-assoc fstᵐ ⟨ g , h ⟩ᵐ f) ⟩
            (fstᵐ ∘ᵐ ⟨ g , h ⟩ᵐ) ∘ᵐ f
          ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ g h) ⟩
            g ∘ᵐ f
          ∎)
         (begin
            sndᵐ ∘ᵐ ⟨ g , h ⟩ᵐ ∘ᵐ f
          ≡⟨ sym (∘ᵐ-assoc sndᵐ ⟨ g , h ⟩ᵐ f) ⟩
            (sndᵐ ∘ᵐ ⟨ g , h ⟩ᵐ) ∘ᵐ f
          ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ g h) ⟩
            h ∘ᵐ f
          ∎))
   ⟩
    ⟨ g , h ⟩ᵐ ∘ᵐ f
  ∎

mapˣᵐ-×ᵐ-assoc⁻¹ : ∀ {A B C A' B' C'} → (f : A →ᵐ A') (g : B →ᵐ B') (h : C →ᵐ C')
                 → mapˣᵐ (mapˣᵐ f g) h ∘ᵐ ×ᵐ-assoc⁻¹ ≡ ×ᵐ-assoc⁻¹ ∘ᵐ mapˣᵐ f (mapˣᵐ g h)
mapˣᵐ-×ᵐ-assoc⁻¹ f g h = 
  begin
    mapˣᵐ (mapˣᵐ f g) h ∘ᵐ ×ᵐ-assoc⁻¹
  ≡⟨⟩
       ⟨ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
    ⟨    (⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ)
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
         (h ∘ᵐ sndᵐ)
      ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (begin
           (⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ fstᵐ)
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ fstᵐ
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ⟩
           ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (⟨⟩ᵐ-∘ᵐ _ _ _) ⟩
        ⟨ (f ∘ᵐ fstᵐ) ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
          (g ∘ᵐ sndᵐ) ∘ᵐ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ cong₂ ⟨_,_⟩ᵐ
          (trans
            (∘ᵐ-assoc _ _ _)
            (trans
              (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              (sym (⟨⟩ᵐ-fstᵐ _ _))))
          (trans
            (∘ᵐ-assoc _ _ _)
            (trans
              (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
              (sym
                (trans
                  (∘ᵐ-assoc _ _ _)
                  (trans
                    (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
                    (trans
                      (sym (∘ᵐ-assoc _ _ _))
                      (trans
                        (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                        (∘ᵐ-assoc _ _ _)))))))) ⟩
        ⟨    fstᵐ
          ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
             (fstᵐ ∘ᵐ sndᵐ)
          ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
      ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
           ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎)
      (begin
           (h ∘ᵐ sndᵐ)
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           h
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ⟩
           h
        ∘ᵐ sndᵐ ∘ᵐ sndᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (h ∘ᵐ sndᵐ)
        ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-congˡ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
           (   sndᵐ
            ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
        ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           sndᵐ
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (⟨⟩ᵐ-sndᵐ _ _)) ⟩
           sndᵐ
        ∘ᵐ sndᵐ
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (sndᵐ ∘ᵐ sndᵐ)
        ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎) ⟩
    ⟨    ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ,
         (sndᵐ ∘ᵐ sndᵐ)
      ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
    ∘ᵐ ⟨ f ∘ᵐ fstᵐ , ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨⟩
    ×ᵐ-assoc⁻¹ ∘ᵐ mapˣᵐ f (mapˣᵐ g h)
  ∎

mapˣᵐ-identity : ∀ {A B} → mapˣᵐ {A} {B} {A} {B} idᵐ idᵐ ≡ idᵐ
mapˣᵐ-identity = 
  begin
    ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ sym (⟨⟩ᵐ-unique _ _ _
       (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
       (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))) ⟩
    idᵐ
  ∎

mapˣᵐ-∘ᵐ : ∀ {A A' A'' B B' B''} → (f : A →ᵐ A') (g : B →ᵐ B') (h : A' →ᵐ A'') (i : B' →ᵐ B'')
         → mapˣᵐ (h ∘ᵐ f) (i ∘ᵐ g) ≡ mapˣᵐ h i ∘ᵐ mapˣᵐ f g
mapˣᵐ-∘ᵐ f g h i = 
  begin
    mapˣᵐ (h ∘ᵐ f) (i ∘ᵐ g)
  ≡⟨⟩
    ⟨ (h ∘ᵐ f) ∘ᵐ fstᵐ , (i ∘ᵐ g) ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
      (sym
        (trans
          (∘ᵐ-assoc _ _ _)
          (trans
            (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
            (sym (∘ᵐ-assoc _ _ _)))))
      (sym
        (trans
          (∘ᵐ-assoc _ _ _)
          (trans
            (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))
            (sym (∘ᵐ-assoc _ _ _))))) ⟩
    ⟨ (h ∘ᵐ fstᵐ) ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ,
      (i ∘ᵐ sndᵐ) ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
    ⟨ h ∘ᵐ fstᵐ , i ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
  ≡⟨⟩
    mapˣᵐ h i ∘ᵐ mapˣᵐ f g
  ∎

mapˣᵐ-⟨⟩ᵐ : ∀ {A B C D E} → (f : A →ᵐ B) (g : A →ᵐ C) (h : B →ᵐ D) (i : C →ᵐ E)
          → ⟨ h ∘ᵐ f , i ∘ᵐ g ⟩ᵐ ≡ mapˣᵐ h i ∘ᵐ ⟨ f , g ⟩ᵐ
mapˣᵐ-⟨⟩ᵐ f g h i = 
  begin
    ⟨ h ∘ᵐ f , i ∘ᵐ g ⟩ᵐ
  ≡⟨ cong₂ ⟨_,_⟩ᵐ
       (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
       (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))) ⟩
    ⟨ (h ∘ᵐ fstᵐ) ∘ᵐ ⟨ f , g ⟩ᵐ ,
      (i ∘ᵐ sndᵐ) ∘ᵐ ⟨ f , g ⟩ᵐ ⟩ᵐ
  ≡⟨ ⟨⟩ᵐ-∘ᵐ _ _ _ ⟩
       mapˣᵐ h i
    ∘ᵐ ⟨ f , g ⟩ᵐ
  ∎

-- SET-INDEXED PRODUCTS

⟨⟩ᵢᵐ-∘ᵐ : ∀ {I} {A B} {C : I → Obj}
        → (f : A →ᵐ B) → (g : ((i : I) → B →ᵐ C i))
        → ⟨ (λ i → g i ∘ᵐ f) ⟩ᵢᵐ ≡ ⟨ g ⟩ᵢᵐ ∘ᵐ f
⟨⟩ᵢᵐ-∘ᵐ f g = 
  begin
    ⟨ (λ i → g i ∘ᵐ f) ⟩ᵢᵐ
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i →
      begin
        projᵐ i ∘ᵐ ⟨ g ⟩ᵢᵐ ∘ᵐ f
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
        (projᵐ i ∘ᵐ ⟨ g ⟩ᵢᵐ) ∘ᵐ f
      ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
        g i ∘ᵐ f
      ∎)) ⟩
    ⟨ g ⟩ᵢᵐ ∘ᵐ f
  ∎

mapⁱˣᵐ : ∀ {I A B} → ((i : I) → A i →ᵐ B i) → Πᵐ I A →ᵐ Πᵐ I B
mapⁱˣᵐ fs = ⟨ (λ i → fs i ∘ᵐ projᵐ i) ⟩ᵢᵐ

mapⁱˣᵐ-identity : ∀ {I A} → mapⁱˣᵐ {I} {A} {A} (λ i → idᵐ) ≡ idᵐ
mapⁱˣᵐ-identity = 
  begin
    mapⁱˣᵐ (λ i → idᵐ)
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i → 
      begin
        projᵐ i ∘ᵐ idᵐ
      ≡⟨ ∘ᵐ-identityʳ _ ⟩
        projᵐ i
      ≡⟨ sym (∘ᵐ-identityˡ _) ⟩
        idᵐ ∘ᵐ projᵐ i
      ∎)) ⟩
    idᵐ
  ∎

mapⁱˣᵐ-∘ᵐ : ∀ {I} {A B C : I → Obj}
          → (f : ((i : I) → A i →ᵐ B i))
          → (g : ((i : I) → B i →ᵐ C i))
          → mapⁱˣᵐ (λ i → g i ∘ᵐ f i) ≡ mapⁱˣᵐ g ∘ᵐ mapⁱˣᵐ f
mapⁱˣᵐ-∘ᵐ f g = 
  begin
    mapⁱˣᵐ (λ i → g i ∘ᵐ f i)
  ≡⟨⟩
    ⟨ (λ i → (g i ∘ᵐ f i) ∘ᵐ projᵐ i) ⟩ᵢᵐ
  ≡⟨ sym (⟨⟩ᵢᵐ-unique _ _ (λ i →
      begin
           projᵐ i
        ∘ᵐ ⟨ (λ i₁ → g i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (   projᵐ i
            ∘ᵐ ⟨ (λ i₁ → g i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ)
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-congˡ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
           (g i ∘ᵐ projᵐ i)
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           g i
        ∘ᵐ projᵐ i
        ∘ᵐ ⟨ (λ i₁ → f i₁ ∘ᵐ projᵐ i₁) ⟩ᵢᵐ
      ≡⟨ ∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ _) ⟩
           g i
        ∘ᵐ f i
        ∘ᵐ projᵐ i
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
        (g i ∘ᵐ f i) ∘ᵐ projᵐ i
      ∎)) ⟩
    ⟨ (λ i → g i ∘ᵐ projᵐ i) ⟩ᵢᵐ ∘ᵐ ⟨ (λ i → f i ∘ᵐ projᵐ i) ⟩ᵢᵐ
  ≡⟨⟩
    mapⁱˣᵐ g ∘ᵐ mapⁱˣᵐ f
  ∎

mapⁱˣᵐ-⟨⟩ᵐ : ∀ {I} {A : Obj} {B C : I → Obj}
           → (f : (i : I) → A →ᵐ B i)
           → (g : (i : I) → B i →ᵐ C i)
           → ⟨ (λ i → g i ∘ᵐ f i) ⟩ᵢᵐ
           ≡ mapⁱˣᵐ g ∘ᵐ ⟨ f ⟩ᵢᵐ
mapⁱˣᵐ-⟨⟩ᵐ {I} {A} {B} {C} f g =
  begin
    ⟨ (λ i → g i ∘ᵐ f i) ⟩ᵢᵐ
  ≡⟨ sym
      (⟨⟩ᵢᵐ-unique _ _
        (λ i → trans (sym (∘ᵐ-assoc _ _ _))
          (trans
            (∘ᵐ-congˡ
              (⟨⟩ᵢᵐ-projᵐ _ i))
              (trans
                (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ (⟨⟩ᵢᵐ-projᵐ _ i)))))) ⟩
    mapⁱˣᵐ g ∘ᵐ ⟨ f ⟩ᵢᵐ
  ∎

-- EXPONENTIALS

appᵐ : ∀ {A B} → (A ⇒ᵐ B) ×ᵐ A →ᵐ B
appᵐ = uncurryᵐ idᵐ

map⇒ᵐ : ∀ {A B C D} → (A →ᵐ B) → (C →ᵐ D) → B ⇒ᵐ C →ᵐ A ⇒ᵐ D
map⇒ᵐ f g = curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)

map⇒ᵐ-identity : ∀ {A B} → map⇒ᵐ {A} {A} {B} {B} idᵐ idᵐ ≡ idᵐ
map⇒ᵐ-identity = 
  begin
    curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-identityˡ _) ⟩
    curryᵐ (uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (⟨⟩ᵐ-unique _ _ _
       (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))
       (trans (∘ᵐ-identityʳ _) (sym (∘ᵐ-identityˡ _)))))) ⟩
    curryᵐ (uncurryᵐ idᵐ ∘ᵐ idᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-identityʳ _) ⟩
    curryᵐ (uncurryᵐ idᵐ)
  ≡⟨ uncurryᵐ-curryᵐ-iso _ ⟩
    idᵐ
  ∎

curryᵐ-mapˣᵐ : ∀ {A B C D E} → (f : C ×ᵐ D →ᵐ E) → (g : A →ᵐ C) → (h : B →ᵐ D)
             → curryᵐ (f ∘ᵐ mapˣᵐ g h) ≡ map⇒ᵐ h idᵐ ∘ᵐ curryᵐ f ∘ᵐ g
curryᵐ-mapˣᵐ f g h = 
  begin
    curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (
      begin
           f
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (sym (curryᵐ-uncurryᵐ-iso _)) ⟩
           uncurryᵐ (curryᵐ f)
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))) ⟩
           uncurryᵐ (idᵐ ∘ᵐ curryᵐ f)
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (uncurryᵐ-nat _ _) ⟩
           (   uncurryᵐ idᵐ
            ∘ᵐ ⟨ curryᵐ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-assoc _ _ _ ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ curryᵐ f ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ g ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (sym (mapˣᵐ-∘ᵐ _ _ _ _)) ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ (curryᵐ f ∘ᵐ g) ∘ᵐ fstᵐ , (idᵐ ∘ᵐ h) ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (cong ⟨ (curryᵐ f ∘ᵐ g) ∘ᵐ fstᵐ ,_⟩ᵐ
          (∘ᵐ-congˡ (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))) ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ (curryᵐ f ∘ᵐ g) ∘ᵐ fstᵐ ,
             (h ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (cong ⟨_,(h ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ (∘ᵐ-congˡ (sym (curryᵐ-nat _ _)))) ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ (curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ fstᵐ ,
             (h ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (cong (⟨_, (h ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ) (∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)))) ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ (idᵐ ∘ᵐ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)) ∘ᵐ fstᵐ ,
             (h ∘ᵐ idᵐ) ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congʳ (mapˣᵐ-∘ᵐ _ _ _ _) ⟩
           uncurryᵐ idᵐ
        ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ
        ∘ᵐ ⟨ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ sym (∘ᵐ-assoc _ _ _) ⟩
           (uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
        ∘ᵐ ⟨ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ≡⟨ ∘ᵐ-congˡ (sym (∘ᵐ-identityˡ _)) ⟩
           (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
        ∘ᵐ ⟨ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
      ∎) ⟩
    curryᵐ (   (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ ⟨ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ curryᵐ-nat _ _ ⟩
       curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ curryᵐ (f ∘ᵐ ⟨ g ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ ∘ᵐ-congʳ (curryᵐ-nat _ _) ⟩
       curryᵐ (idᵐ ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , h ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ curryᵐ f
    ∘ᵐ g
  ∎

curryᵐ-map⇒ᵐ : ∀ {A B C D}
             → (f : A ×ᵐ B →ᵐ C) → (g : C →ᵐ D)
             → curryᵐ (g ∘ᵐ f) ≡ map⇒ᵐ idᵐ g ∘ᵐ curryᵐ f
curryᵐ-map⇒ᵐ {A} {B} {C} {D} f g = 
  begin
    curryᵐ (g ∘ᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (curryᵐ-uncurryᵐ-iso _))) ⟩
    curryᵐ (g ∘ᵐ uncurryᵐ (curryᵐ f))
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _)))) ⟩
    curryᵐ (g ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ (curryᵐ f)))
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (uncurryᵐ-nat _ _)) ⟩
    curryᵐ (g ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ (curryᵐ f) idᵐ)
  ≡⟨ cong curryᵐ (sym (∘ᵐ-assoc _ _ _)) ⟩
    curryᵐ ((g ∘ᵐ uncurryᵐ idᵐ) ∘ᵐ mapˣᵐ (curryᵐ f) idᵐ)
  ≡⟨ curryᵐ-nat _ _ ⟩
       curryᵐ (g ∘ᵐ uncurryᵐ idᵐ)
    ∘ᵐ curryᵐ f
  ≡⟨ ∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))))) ⟩
       curryᵐ (g ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ idᵐ))
    ∘ᵐ curryᵐ f
  ≡⟨ ∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ (uncurryᵐ-nat _ _))) ⟩
       curryᵐ (g ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ curryᵐ f
  ∎

map⇒ᵐ-∘ᵐ : ∀ {A B C D E F}
         → (f : C →ᵐ B) → (g : B →ᵐ A)
         → (h : D →ᵐ E) → (i : E →ᵐ F)
         → map⇒ᵐ (g ∘ᵐ f) (i ∘ᵐ h)
         ≡ map⇒ᵐ f i ∘ᵐ map⇒ᵐ g h

map⇒ᵐ-∘ᵐ {A} {B} {C} {D} {E} {F} f g h i = 
  begin
    curryᵐ (   (i ∘ᵐ h)
            ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , (g ∘ᵐ f) ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-assoc _ _ _) ⟩
    curryᵐ (   i
            ∘ᵐ h
            ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , (g ∘ᵐ f) ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (trans
       (cong₂ mapˣᵐ (sym (∘ᵐ-identityˡ _)) refl) (mapˣᵐ-∘ᵐ _ _ _ _))))) ⟩
    curryᵐ (   i
            ∘ᵐ h
            ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
    curryᵐ (   i
            ∘ᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (sym (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)))) ⟩
    curryᵐ (   i
            ∘ᵐ uncurryᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ))
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (cong uncurryᵐ (sym (∘ᵐ-identityˡ _))))) ⟩
    curryᵐ (   i
            ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)))
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congˡ (uncurryᵐ-nat _ _))) ⟩
    curryᵐ (   i
            ∘ᵐ (   uncurryᵐ idᵐ
                ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ)
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
    curryᵐ (   i
            ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ
            ∘ᵐ mapˣᵐ idᵐ f)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (trans
       (cong₂ mapˣᵐ (sym (∘ᵐ-identityʳ _)) (sym (∘ᵐ-identityˡ _))) (mapˣᵐ-∘ᵐ _ _ _ _))))) ⟩
    curryᵐ (   i
            ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨ curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ ,
                 f ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (cong₂ ⟨_,_⟩ᵐ refl (∘ᵐ-congʳ (sym (∘ᵐ-identityˡ _)))))) ⟩
    curryᵐ (   i ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨ curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ) ∘ᵐ fstᵐ ,
                 f ∘ᵐ idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (sym (cong₂ ⟨_,_⟩ᵐ
      (trans (∘ᵐ-assoc _ _ _) (trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (∘ᵐ-identityˡ _)))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))))) ⟩
    curryᵐ (   i ∘ᵐ uncurryᵐ idᵐ
            ∘ᵐ ⟨    (idᵐ ∘ᵐ fstᵐ)
                 ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ ,
                    (f ∘ᵐ sndᵐ)
                 ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ ⟩ᵐ)
  ≡⟨ cong curryᵐ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ᵐ _ _ _))) ⟩
    curryᵐ (   i ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , f ∘ᵐ sndᵐ ⟩ᵐ
            ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ)
  ≡⟨ cong curryᵐ (sym (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))) ⟩
    curryᵐ (   (i ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , f ∘ᵐ sndᵐ ⟩ᵐ)
            ∘ᵐ mapˣᵐ (curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)) idᵐ)
  ≡⟨ curryᵐ-nat _ _ ⟩
       curryᵐ (i ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , f ∘ᵐ sndᵐ ⟩ᵐ)
    ∘ᵐ curryᵐ (h ∘ᵐ uncurryᵐ idᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ)
  ∎

map⇒ᵐ-∘ᵐʳ : ∀ {A B C D}
          → (f : B →ᵐ C)
          → (g : C →ᵐ D)
          → map⇒ᵐ (idᵐ {A}) (g ∘ᵐ f)
          ≡ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ idᵐ f

map⇒ᵐ-∘ᵐʳ {A} {B} {C} {D} f g = 
  begin
    map⇒ᵐ idᵐ (g ∘ᵐ f)
  ≡⟨ cong₂ map⇒ᵐ (sym (∘ᵐ-identityˡ _)) refl ⟩
    map⇒ᵐ (idᵐ ∘ᵐ idᵐ) (g ∘ᵐ f)
  ≡⟨ map⇒ᵐ-∘ᵐ _ _ _ _ ⟩
    map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ idᵐ f
  ∎

uncurryᵐ-mapˣᵐ : ∀ {A B C D E}
               → (f : B →ᵐ D ⇒ᵐ E)
               → (g : A →ᵐ B)
               → (h : C →ᵐ D)
               → uncurryᵐ (map⇒ᵐ h idᵐ ∘ᵐ f ∘ᵐ g)
               ≡ uncurryᵐ f ∘ᵐ mapˣᵐ g h
               
uncurryᵐ-mapˣᵐ {A} {B} {C} {D} {E} f g h =
  begin
    uncurryᵐ (   map⇒ᵐ h idᵐ
              ∘ᵐ f
              ∘ᵐ g)
  ≡⟨⟩
    uncurryᵐ
      (   curryᵐ (   idᵐ
                  ∘ᵐ uncurryᵐ idᵐ
                  ∘ᵐ mapˣᵐ idᵐ h)
       ∘ᵐ f
       ∘ᵐ g)
  ≡⟨ uncurryᵐ-nat _ _ ⟩
       uncurryᵐ
         (curryᵐ (   idᵐ
                  ∘ᵐ uncurryᵐ idᵐ
                  ∘ᵐ mapˣᵐ idᵐ h))
    ∘ᵐ mapˣᵐ (f ∘ᵐ g) idᵐ
  ≡⟨ trans
      (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _))
      (trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
       idᵐ
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ idᵐ h
    ∘ᵐ mapˣᵐ (f ∘ᵐ g) idᵐ
  ≡⟨ ∘ᵐ-identityˡ _ ⟩
       uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ idᵐ h
    ∘ᵐ mapˣᵐ (f ∘ᵐ g) idᵐ
  ≡⟨ ∘ᵐ-congʳ
      (trans
        (sym (mapˣᵐ-∘ᵐ _ _ _ _))
        (sym
          (trans
            (sym (mapˣᵐ-∘ᵐ _ _ _ _))
            (cong₂ mapˣᵐ
              (sym (∘ᵐ-identityˡ _))
              (trans (∘ᵐ-identityˡ _) (sym (∘ᵐ-identityʳ _))))))) ⟩
       uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ f idᵐ
    ∘ᵐ mapˣᵐ g h
  ≡⟨ trans (sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (sym (uncurryᵐ-nat _ _))) ⟩
       uncurryᵐ (idᵐ ∘ᵐ f)
    ∘ᵐ mapˣᵐ g h
  ≡⟨ ∘ᵐ-congˡ (cong uncurryᵐ (∘ᵐ-identityˡ _)) ⟩
       uncurryᵐ f
    ∘ᵐ mapˣᵐ g h
  ≡⟨⟩
       uncurryᵐ f
    ∘ᵐ mapˣᵐ g h
  ∎

uncurryᵐ-map⇒ᵐ : ∀ {A B C D}
               → (f : A →ᵐ B ⇒ᵐ C)
               → (g : C →ᵐ D)
               → uncurryᵐ (map⇒ᵐ idᵐ g ∘ᵐ f)
               ≡ g ∘ᵐ uncurryᵐ f

uncurryᵐ-map⇒ᵐ {A} {B} {C} {D} f g =
  begin
    uncurryᵐ (map⇒ᵐ idᵐ g ∘ᵐ f)
  ≡⟨⟩
    uncurryᵐ (   curryᵐ (g ∘ᵐ uncurryᵐ idᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)
              ∘ᵐ f)
  ≡⟨ cong uncurryᵐ (∘ᵐ-congˡ (cong curryᵐ (∘ᵐ-congʳ (trans (∘ᵐ-congʳ mapˣᵐ-identity) (∘ᵐ-identityʳ _))))) ⟩
    uncurryᵐ (   curryᵐ (g ∘ᵐ uncurryᵐ idᵐ)
              ∘ᵐ f)
  ≡⟨ uncurryᵐ-nat _ _ ⟩
       uncurryᵐ (curryᵐ (g ∘ᵐ uncurryᵐ idᵐ))
    ∘ᵐ mapˣᵐ f idᵐ
  ≡⟨ trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)) (∘ᵐ-assoc _ _ _) ⟩
       g
    ∘ᵐ uncurryᵐ idᵐ
    ∘ᵐ mapˣᵐ f idᵐ
  ≡⟨ ∘ᵐ-congʳ (sym (uncurryᵐ-nat _ _)) ⟩
      g
    ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ f)
  ≡⟨ ∘ᵐ-congʳ (cong uncurryᵐ (∘ᵐ-identityˡ _)) ⟩
      g
    ∘ᵐ uncurryᵐ f
  ∎
