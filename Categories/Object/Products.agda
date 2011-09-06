{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Products {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

import Categories.Object.Terminal as Terminal
import Categories.Object.BinaryProducts as BinaryProducts

open Terminal C
open BinaryProducts C

-- this should really be 'FiniteProducts', no?
record Products : Set (o ⊔ ℓ ⊔ e) where
  field
    terminal : Terminal
    binary : BinaryProducts
