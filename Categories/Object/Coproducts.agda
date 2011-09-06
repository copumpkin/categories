{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Coproducts {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

import Categories.Object.Initial as Initial
import Categories.Object.BinaryCoproducts as BinaryCoproducts

open Initial C
open BinaryCoproducts C

-- this should really be 'FiniteCoproducts', no?
record Coproducts : Set (o ⊔ ℓ ⊔ e) where
  field
    initial : Initial
    binary : BinaryCoproducts