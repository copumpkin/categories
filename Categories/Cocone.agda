{-# OPTIONS --universe-polymorphism #-}
module Categories.Cocone where

open import Level

open import Categories.Operations
open import Categories.Category
open import Categories.Functor hiding (_≡_)

record Cocone {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} (F : Functor J C) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  module J = Category J
  open Category C
  open Functor F
  field
    N : Obj
    ψ : ∀ X → ((F₀ X) ⇒ N)
    .commute : ∀ {X Y} (f : J [ X , Y ]) → ψ X ≡ ψ Y ∘ F₁ f
