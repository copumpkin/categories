{-# OPTIONS --universe-polymorphism #-}
module Categories.Presheaf where

open import Categories.Category
open import Categories.Functor

Presheaf : ∀ {o a} {o′ a′} (C : Category o a) (V : Category o′ a′) → Set _
Presheaf C V = Functor C.op V
  where module C = Category C