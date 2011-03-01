{-# OPTIONS --universe-polymorphism #-}
module Category.Presheaf where

open import Category
open import Category.Functor

Presheaf : ∀ {o ℓ e} {o′ ℓ′ e′} (C : Category o ℓ e) (V : Category o′ ℓ′ e′) → Set _
Presheaf C V = Functor C.op V
  where module C = Category.Category C