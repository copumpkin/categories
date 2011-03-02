{-# OPTIONS --universe-polymorphism #-}
module Category.Limit where

open import Support
open import Category
open import Category.Functor
open import Category.Cones
open import Category.Object.Terminal

-- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
record Limit {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    initial : Terminal (Cones F)