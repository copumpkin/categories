{-# OPTIONS --universe-polymorphism #-}

module Category.NaturalIsomorphism where

open import Support
open import Category
open import Category.Functor hiding (id) renaming (_∘_ to _∘F_)
open import Category.NaturalTransformation
import Category.Morphisms as Morphisms

record NaturalIsomorphism {o ℓ e o′ ℓ′ e′}
                          {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  open Morphisms D

  field
    .iso : ∀ X → Iso (⇒.η X) (⇐.η X)