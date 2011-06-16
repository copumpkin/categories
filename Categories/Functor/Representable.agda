{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Representable where

open import Level

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.NaturalIsomorphism

record Representable {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ suc ℓ ⊔ suc e) where
  module C = Category C
  field
    F : Functor C (ISetoids ℓ e)
    A : C.Obj
    Iso : NaturalIsomorphism F (Hom[_,-] {C = C} A)
