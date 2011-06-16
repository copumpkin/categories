{-# OPTIONS --universe-polymorphism #-}
module Categories.Limit where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Cones
open import Categories.Object.Terminal

-- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
record Limit {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    initial : Terminal (Cones F)