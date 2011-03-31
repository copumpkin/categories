{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal where

open import Support hiding (_×_)
open import Category

open import Category.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Category.NaturalIsomorphism
open import Category.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)
open import Category.Functor.Constant

open import Category.Monoidal.Helpers

record Monoidal {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ; assoc)

  field
    ⊗  : Bifunctor C C C
    id : Obj

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  open MonoidalHelperFunctors C ⊗ id

  field
    identityˡ : NaturalIsomorphism id⊗x idF
    identityʳ : NaturalIsomorphism x⊗id idF
    assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]

  open Coherence identityˡ identityʳ assoc

  field
    .triangle : TriangleLeftSide ≡ⁿ (TriangleRightSide ∘₁ TriangleTopSide)
    .pentagon : (PentagonNESide ∘₁ PentagonNWSide) ≡ⁿ (PentagonSESide ∘₁ (PentagonSSide ∘₁ PentagonSWSide))