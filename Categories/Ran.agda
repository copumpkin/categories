module Categories.Ran where

open import Level
open import Categories.Category
open import Categories.Functor hiding (_≡_)
open import Categories.NaturalTransformation

record Ran {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} 
           {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
           (F : Functor A B) (X : Functor A C) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  field
    R : Functor B C
    η : NaturalTransformation (R ∘ F) X

    δ : (M : Functor B C) → (α : NaturalTransformation (M ∘ F) X) → NaturalTransformation M R

    .δ-unique : {M : Functor B C} → {α : NaturalTransformation (M ∘ F) X} → 
                (δ′ : NaturalTransformation M R) → α ≡ η ∘₁ (δ′ ∘ʳ F) → δ′ ≡ δ M α
    .commutes : (M : Functor B C) → (α : NaturalTransformation (M ∘ F) X) → α ≡ η ∘₁ (δ M α ∘ʳ F)
