{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal where

open import Support hiding (_×_)
open import Category hiding (id)

open import Category.Bifunctor

record Monoidal {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category.Category C
  field
    _⊗_ : Bifunctor C C C
    id   : Obj

