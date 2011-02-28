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
    α : Hom (F₀ A) A
