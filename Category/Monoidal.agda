{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal where

open import Support hiding (_×_)
open import Category

open import Category.Bifunctor using (Bifunctor)
open import Category.NaturalIsomorphism
open import Category.NaturalTransformation using (_∘₁_) renaming (_≡_ to _≡ⁿ_)

open import Category.Monoidal.Helpers

record Monoidal {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ; assoc)

  field
    ⊗  : Bifunctor C C C
    id : Obj

  open MonoidalHelperFunctors C ⊗ id

  field
    identityˡ : NaturalIsomorphism id⊗x x
    identityʳ : NaturalIsomorphism x⊗id x
    assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]

  open Coherence identityˡ identityʳ assoc

  field
    .triangle : TriangleLeftSide ≡ⁿ (TriangleRightSide ∘₁ TriangleTopSide)
    .pentagon : (PentagonNESide ∘₁ PentagonNWSide) ≡ⁿ (PentagonSESide ∘₁ (PentagonSSide ∘₁ PentagonSWSide))