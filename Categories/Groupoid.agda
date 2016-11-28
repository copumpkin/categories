{-# OPTIONS --universe-polymorphism #-}
module Categories.Groupoid where

open import Level

open import Categories.Category
import Categories.Morphisms

record Groupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  open C using (_⇒_) 

  open Categories.Morphisms C

  field
    _⁻¹  : ∀ {A B} → (A ⇒ B) → (B ⇒ A)
    .iso : ∀ {A B} {f : A ⇒ B} → Iso f (f ⁻¹)

