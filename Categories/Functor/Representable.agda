{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Representable where

open import Level

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.NaturalIsomorphism

record Representable {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ suc ℓ ⊔ suc e) where
  open Category C
  open Hom C
  field
    F : Functor C (ISetoids ℓ e) -- should this be a parameter to the record?
    A : Obj
    Iso : NaturalIsomorphism F Hom[ A ,-]
