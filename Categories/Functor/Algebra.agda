{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Algebra where

open import Level hiding (lift)

open import Categories.Category
open import Categories.Functor

record F-Algebra {o ℓ e} {C : Category o ℓ e} (F : Endofunctor C) : Set (o ⊔ ℓ) where
  constructor _,_
  open Category C
  open Functor F
  field
    A : Obj
    α : F₀ A ⇒ A

lift : ∀ {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} → F-Algebra F → F-Algebra F
lift {F = F} (A , α) = record { A = F₀ A; α = F₁ α }
  where
  open Functor F