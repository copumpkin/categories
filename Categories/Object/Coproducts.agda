{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Coproducts {o a} (C : Category o a) where

open Category C

open import Level

import Categories.Object.Initial as Initial
import Categories.Object.BinaryCoproducts as BinaryCoproducts

open Initial C
open BinaryCoproducts C

-- this should really be 'FiniteCoproducts', no?
record Coproducts : Set (o ⊔ a) where
  field
    initial : Initial
    binary : BinaryCoproducts