{-# OPTIONS --universe-polymorphism #-}
module Category.Adjunction where

open import Support
open import Category
open import Category.Functor renaming (id to idF; _≡_ to _≡F_)
open import Category.NaturalTransformation

record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} (F : Functor D C) (G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  field
    unit   : NaturalTransformation idF (G ∘ F)
    counit : NaturalTransformation (F ∘ G) idF

    .zig : id ≡ (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : id ≡ (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)