{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

import Categories.Object.Product as Product

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    product : Product.Product C (B^A) B

  open Product.Product C product renaming (A×B to B^A×B)

  field
    eval : B^A×B ⇒ B
    λg : ∀ X → (P : Product.Product C X A) → (Product.Product.A×B C P ⇒ B)
    -- moar