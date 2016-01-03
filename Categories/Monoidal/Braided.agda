{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Braided where

open import Level
open import Level using (_⊔_)

open import Categories.Category

open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₁_) renaming (_≡_ to _≡ⁿ_)

open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers

open import Categories.Monoidal

record Braided {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  private module M = Monoidal M
  open C hiding (id; identityˡ; identityʳ; assoc)
  open M

  open MonoidalHelperFunctors C ⊗ id
  open BraidedHelperFunctors C ⊗ id

  field
    braid : NaturalIsomorphism x⊗y y⊗x
    
  open Braiding identityˡ identityʳ assoc braid

  field
    -- NB: Triangle is redundant, proof coming soon...
    -- But until it does, use this.
    -- note that this diagram is the "opposite" than the one from the Wikipedia page.
    .unit-coh : BTriangleLeft ≡ⁿ (BTriangleRight ∘₁ BTriangleTop)

    .hexagon₁ : (Hexagon1SideB ∘₁ (Hexagon1TopB ∘₁ Hexagon1TopA)) ≡ⁿ (Hexagon1BottomB ∘₁ (Hexagon1BottomA ∘₁ Hexagon1SideA))
    .hexagon₂ : (Hexagon2SideB ∘₁ (Hexagon2TopB ∘₁ Hexagon2TopA)) ≡ⁿ (Hexagon2BottomB ∘₁ (Hexagon2BottomA ∘₁ Hexagon2SideA))
