{-# OPTIONS --universe-polymorphism #-}

open import Support hiding (_×_)
open import Category

module Category.Object.Products {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

import Category.Object.Product as Product
import Category.Object.Terminal as Terminal
import Category.Morphisms as Morphisms

open Product C
open Terminal C
open Morphisms C

record Products : Set (o ⊔ ℓ ⊔ e) where
  field
    terminal : Terminal
    binary : BinaryProducts
