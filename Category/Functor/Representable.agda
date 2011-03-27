{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Representable where

open import Support
open import Category
open import Category.Agda
open import Category.Functor using (Functor)
open import Category.Functor.Hom
open import Category.NaturalIsomorphism

record Representable {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ suc ℓ ⊔ suc e) where
  module C = Category.Category C
  field
    F : Functor C (Setoids ℓ e)
    A : C.Obj
    Iso : NaturalIsomorphism F (Hom[_,-] {C = C} A)
