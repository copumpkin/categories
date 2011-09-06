{-# OPTIONS --universe-polymorphism #-}
module Categories.Cocone where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; _∘_)

record Cocone {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  module J = Category J
  open Category C
  open Functor F
  field
    N : Obj
    ψ : ∀ X → ((F₀ X) ⇒ N)
    .commute : ∀ {X Y} (f : J [ X , Y ]) → ψ X ≡ ψ Y ∘ F₁ f
