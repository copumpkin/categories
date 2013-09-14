{-# OPTIONS --universe-polymorphism #-}
module Categories.Lan where

open import Level
open import Categories.Category
open import Categories.Functor hiding (_≡_)
open import Categories.NaturalTransformation

record Lan {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} 
           {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
           (F : Functor A B) (X : Functor A C) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  field
    L : Functor B C
    ε : NaturalTransformation X (L ∘ F)

    σ : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → NaturalTransformation L M

    .σ-unique : {M : Functor B C} → {α : NaturalTransformation X (M ∘ F)} → 
                (σ′ : NaturalTransformation L M) → α ≡ (σ′ ∘ʳ F) ∘₁ ε → σ′ ≡ σ M α
    .commutes : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → α ≡ (σ M α ∘ʳ F) ∘₁ ε
