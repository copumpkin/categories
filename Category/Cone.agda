{-# OPTIONS --universe-polymorphism #-}
module Category.Cone where

open import Support
open import Category
open import Category.Functor hiding (_≡_; _∘_)

record Cone {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  module J = Category.Category J
  open Category.Category C
  open Functor F
  field
    N : Obj
    ψ : ∀ X → (N ⇒ (F₀ X))
    .commute : ∀ {X Y} (f : J [ X , Y ]) → F₁ f ∘ ψ X ≡ ψ Y
