{-# OPTIONS --universe-polymorphism #-}
module Categories.Colimit where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Cocones
open import Categories.Object.Initial

-- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
record Colimit {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} (F : Functor J C) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    initial : Initial (Cocones F)

record Cocomplete (o a : Level) {o′ a′} (C : Category o′ a′) : Set (suc o ⊔ suc a ⊔ o′ ⊔ a′) where
  field
    colimit : ∀ {J : Category o a} (F : Functor J C) → Colimit F