{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Symmetric where

open import Level

open import Categories.Category
open import Categories.Monoidal
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₁_; _≡_; id)

record Symmetric {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (B : Braided M) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  private module M = Monoidal M
  private module B = Braided B

  -- open C hiding (id; identityˡ; identityʳ; assoc; _≡_)
  -- open M hiding (id)
  -- open MonoidalHelperFunctors C ⊗ M.id
  -- open BraidedHelperFunctors C ⊗ M.id

  private module NI = NaturalIsomorphism B.braid
  
  field
    symmetry : NI.F⇒G ∘₁ NI.F⇐G ≡ id
