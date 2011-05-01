{-# OPTIONS --universe-polymorphism #-}

open import Support hiding (⊤)
open import Category

module Category.Object.SubobjectClassifier {o ℓ e} (C : Category o ℓ e) where

open Category.Category C
open import Category.Object.Terminal

open import Category.Morphisms
open import Category.Pullback

record SubobjectClassifier : Set (o ⊔ ℓ ⊔ e) where
  field
    Ω : Obj
    χ : ∀ {U X} → (j : U ⇒ X) → (X ⇒ Ω)
    terminal : Terminal C

  open Terminal C terminal

  field
    ⊤⇒Ω : ⊤ ⇒ Ω
    .j-pullback : ∀ {U X} → (j : U ⇒ X) → Mono C j → Pullback C ⊤⇒Ω (χ j)
    .χ-unique : ∀ {U X} → (j : U ⇒ X) → (χ′ : X ⇒ Ω) → Mono C j → Pullback C ⊤⇒Ω χ′ → χ′ ≡ χ j

