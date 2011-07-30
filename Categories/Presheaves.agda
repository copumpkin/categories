{-# OPTIONS --universe-polymorphism #-}
module Categories.Presheaves where

open import Level

open import Categories.Category
open import Categories.Agda
open import Categories.FunctorCategory

Presheaves : ∀ {o ℓ e : Level} → Category o ℓ e → Category _ _ _
Presheaves {o} {ℓ} {e} C = Functors (Category.op C) (ISetoids ℓ e)