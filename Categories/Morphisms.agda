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

infix 4 _ⓘ_
_ⓘ_ : ∀ {X Y Z} → Y ≅ Z → X ≅ Y → X ≅ Z
G ⓘ F = record
  { f = G.f ∘ F.f
  ; g = F.g ∘ G.g
  ; iso = record
    { isoˡ = 
      begin
        (F.g ∘ G.g) ∘ (G.f ∘ F.f)
      ↓⟨ assoc ⟩
        F.g ∘ (G.g ∘ (G.f ∘ F.f))
      ↑⟨ refl ⟩∘⟨ assoc ⟩
        F.g ∘ (G.g ∘ G.f) ∘ F.f
      ↓⟨ refl ⟩∘⟨ isoˡ G.iso ⟩∘⟨ refl ⟩
        F.g ∘ (id ∘ F.f)
      ↓⟨ refl ⟩∘⟨ identityˡ ⟩
        F.g ∘ F.f
      ↓⟨ isoˡ F.iso ⟩
        id
      ∎
    ; isoʳ = 
      begin
        (G.f ∘ F.f) ∘ (F.g ∘ G.g)
      ↓⟨ assoc ⟩
        G.f ∘ (F.f ∘ (F.g ∘ G.g))
      ↑⟨ refl ⟩∘⟨ assoc ⟩
        G.f ∘ (F.f ∘ F.g) ∘ G.g
      ↓⟨ refl ⟩∘⟨ isoʳ F.iso ⟩∘⟨ refl ⟩
        G.f ∘ (id ∘ G.g)
      ↓⟨ refl ⟩∘⟨ identityˡ ⟩
        G.f ∘ G.g
      ↓⟨ isoʳ G.iso ⟩
        id
      ∎
    }
  }
  where
  module F = _≅_ F
  module G = _≅_ G
  open Iso
  open Equiv
  open HomReasoning