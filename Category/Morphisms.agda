{-# OPTIONS --universe-polymorphism #-}
open import Category

module Category.Morphisms {o ℓ e} (C : Category o ℓ e) where

open import Support
open Category.Category C

Mono : ∀ {A B} → (f : Hom A B) → Set _
Mono {A} f = ∀ {C} → (g₁ g₂ : Hom C A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂

Epi : ∀ {B A} → (f : Hom A B) → Set _
Epi {B} f = ∀ {C} → (g₁ g₂ : Hom B C) → g₁ ∘ f ≡ g₂ ∘ f → g₁ ≡ g₂

record Iso {A B} (f : Hom A B) (g : Hom B A) : Set (o ⊔ ℓ ⊔ e) where
  field
    .isoˡ : g ∘ f ≡ id
    .isoʳ : f ∘ g ≡ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    f : Hom A B
    g : Hom B A
    .iso : Iso f g

