{-# OPTIONS --universe-polymorphism #-}

open import Support hiding (_×_)
open import Category

module Category.Object.Products {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

import Category.Object.Terminal as Terminal
import Category.Object.BinaryProducts as BinaryProducts

open Terminal C
open BinaryProducts C

record Products : Set (o ⊔ ℓ ⊔ e) where
  field
    terminal : Terminal
    binary : BinaryProducts
