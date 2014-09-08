{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)

record Monad {o a} (C : Category o a) : Set (o ⊔ a) where
  field
    F : Endofunctor C
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘ F) F

  module F = Functor F
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  open η public using () renaming (η to η[_])
  open μ public using () renaming (η to μ[_])

  open Functor F

  field
    .assoc     : μ ∘₁ (F ∘ˡ μ) ≡ μ ∘₁ (μ ∘ʳ F)
    .identityˡ : μ ∘₁ (F ∘ˡ η) ≡ idN
    .identityʳ : μ ∘₁ (η ∘ʳ F) ≡ idN