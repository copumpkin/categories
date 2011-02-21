{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Object.SubobjectClassifier {o ℓ e} (C : Category o ℓ e) where

open Category.Category C
open import Category.Object.Terminal

open import Category.Morphisms
open import Category.Pullback

record SubobjectClassifier : Set (o ⊔ ℓ ⊔ e) where
  field
    Ω : Obj
    χ : ∀ {U X} → (j : Hom U X) → Hom X Ω
    terminal : Terminal C

  open Terminal C terminal

  field
    ⊤⇒Ω : Hom ⊤ Ω
    .j-pullback : ∀ {U X} → (j : Hom U X) → Mono C j → Pullback C ⊤⇒Ω (χ j)
    .χ-unique : ∀ {U X} → (j : Hom U X) → (χ′ : Hom X Ω) → Mono C j → Pullback C ⊤⇒Ω χ′ → χ′ ≡ χ j

