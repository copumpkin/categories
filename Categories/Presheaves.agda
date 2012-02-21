{-# OPTIONS --universe-polymorphism #-}
module Categories.Presheaves where

open import Level

open import Categories.Category
open import Categories.Agda
open import Categories.FunctorCategory

Presheaves : ∀ {o a : Level} → Category o a → Category _ _
Presheaves {o} {a} C = Functors (Category.op C) (Sets a)