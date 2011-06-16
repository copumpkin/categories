{-# OPTIONS --universe-polymorphism #-}
module Categories.Presheaf where

open import Categories.Category
open import Categories.Functor

Presheaf : ∀ {o ℓ e} {o′ ℓ′ e′} (C : Category o ℓ e) (V : Category o′ ℓ′ e′) → Set _
Presheaf C V = Functor C.op V
  where module C = Category C