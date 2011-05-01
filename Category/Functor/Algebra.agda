{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Algebra where

open import Support
open import Category
open import Category.Functor

record F-Algebra {o ℓ e} {C : Category o ℓ e} (F : Endofunctor C) : Set (o ⊔ ℓ) where
  constructor _,_
  open Category.Category C
  open Functor F
  field
    A : Obj
    α : F₀ A ⇒ A

lift : ∀ {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} → F-Algebra F → F-Algebra F
lift {F = F} (A , α) = record { A = F₀ A; α = F₁ α }
  where
  open Functor F