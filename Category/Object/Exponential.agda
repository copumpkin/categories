{-# OPTIONS --universe-polymorphism #-}
open import Category

module Category.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open import Support hiding (_×_)
open Category.Category C

import Category.Object.Product as Product

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    product : Product.Product C (B^A) B

  open Product.Product C product renaming (A×B to B^A×B)

  field
    eval : Hom B^A×B B
    λg : ∀ X → (P : Product.Product C X A) → Hom (Product.Product.A×B C P) B
    -- moar