---------------------------------------------
-- Interpretation of base and ground types --
---------------------------------------------

open import Semantics.Model.Category
open import Semantics.Model.Modality.Future

module Semantics.Model.BaseGroundTypes (Cat : Category)
                                       (Fut : Future Cat) where

open import Util.Operations

open Category Cat
open Future Fut

record BaseGroundTypes : Set₁ where

  field
  
    -- base type interpretation
    
    ConstObj : BaseType → Obj

    -- interpretation of base-typed constants
    
    constᵐ : ∀ {B} → BaseSet B → 𝟙ᵐ →ᵐ ConstObj B

  -- extension of base type interpretation to ground types
  
  ⟦_⟧ᵍ : GType → Obj
  ⟦ Base B ⟧ᵍ   = ConstObj B
  ⟦ Unit ⟧ᵍ     = 𝟙ᵐ
  ⟦ Empty ⟧ᵍ    = 𝟘ᵐ
  ⟦ A |×|ᵍ B ⟧ᵍ = ⟦ A ⟧ᵍ ×ᵐ ⟦ B ⟧ᵍ
  ⟦ [ τ ]ᵍ A ⟧ᵍ = [ τ ]ᵒ ⟦ A ⟧ᵍ
