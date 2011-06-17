{-# OPTIONS --universe-polymorphism #-}
module Categories.Lan where

open import Level
open import Categories.Category
open import Categories.Functor hiding (_≡_)
open import Categories.NaturalTransformation

record Lan {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} 
           {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
           (X : Functor A C) (F : Functor A B) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  field
    L : Functor B C
    ε : NaturalTransformation X (L ∘ F)

    σ : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → NaturalTransformation L M

    .σ-unique : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → (σ′ : NaturalTransformation L M) → σ′ ≡ σ M α

  σ′ : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → NaturalTransformation (L ∘ F) (M ∘ F)
  σ′ M α = record 
    { η = λ a → NaturalTransformation.η (σ M α) (Functor.F₀ F a)
    ; commute = λ f → NaturalTransformation.commute (σ M α) (Functor.F₁ F f)
    }

  field
    .commutes : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → α ≡ σ′ M α ∘₁ ε