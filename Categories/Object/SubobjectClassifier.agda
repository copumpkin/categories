{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.SubobjectClassifier {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Object.Terminal
open import Categories.Morphisms
open import Categories.Pullback

record SubobjectClassifier : Set (o ⊔ ℓ ⊔ e) where
  field
    Ω : Obj
    χ : ∀ {U X} → (j : U ⇒ X) → (X ⇒ Ω)
    terminal : Terminal C

  open Terminal terminal

  field
    ⊤⇒Ω : ⊤ ⇒ Ω
    .j-pullback : ∀ {U X} → (j : U ⇒ X) → Mono C j → Pullback C ⊤⇒Ω (χ j)
    .χ-unique : ∀ {U X} → (j : U ⇒ X) → (χ′ : X ⇒ Ω) → Mono C j → Pullback C ⊤⇒Ω χ′ → χ′ ≡ χ j

