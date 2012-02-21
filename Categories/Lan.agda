{-# OPTIONS --universe-polymorphism #-}
module Categories.Lan where

open import Level
open import Categories.Category
open import Categories.Functor hiding (_≡_)
open import Categories.NaturalTransformation

record Lan {o₀ a₀} {o₁ a₁} {o₂ a₂} 
           {A : Category o₀ a₀} {B : Category o₁ a₁} {C : Category o₂ a₂}
           (X : Functor A C) (F : Functor A B) : Set (o₀ ⊔ a₀ ⊔ o₁ ⊔ a₁ ⊔ o₂ ⊔ a₂) where
  field
    L : Functor B C
    ε : NaturalTransformation X (L ∘ F)

    σ : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → NaturalTransformation L M

    .σ-unique : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → (σ′ : NaturalTransformation L M) → σ′ ≡ σ M α
    .commutes : (M : Functor B C) → (α : NaturalTransformation X (M ∘ F)) → α ≡ (σ M α ∘ʳ F) ∘₁ ε