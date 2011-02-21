{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Object.Terminal {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

record Terminal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤ : Obj
    ! : ∀ {A} → Hom A ⊤
    !-unique : ∀ {A} → (f : Hom A ⊤) → ! ≡ f
 