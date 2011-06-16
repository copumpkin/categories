{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Morphisms {o ℓ e} (C : Category o ℓ e) where

open import Level
open Category C

Mono : ∀ {A B} → (f : A ⇒ B) → Set _
Mono {A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂

Epi : ∀ {B A} → (f : A ⇒ B) → Set _
Epi {B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≡ g₂ ∘ f → g₁ ≡ g₂

record Iso {A B} (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    .isoˡ : g ∘ f ≡ id
    .isoʳ : f ∘ g ≡ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    f : A ⇒ B
    g : B ⇒ A
    .iso : Iso f g