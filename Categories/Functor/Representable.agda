{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Representable where

open import Level

open import Categories.Category
open import Categories.Agda
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.NaturalIsomorphism

record Representable {o a} (C : Category o a) : Set (o ⊔ suc a) where
  open Category C
  open Hom C
  field
    F : Functor C (Sets a) -- should this be a parameter to the record?
    A : Obj
    Iso : NaturalIsomorphism F Hom[ A ,-]
