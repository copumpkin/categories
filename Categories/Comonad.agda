module Categories.Comonad where

open import Level using (_⊔_)

open import Categories.Category using (Category)
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)

record Comonad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    ε : NaturalTransformation F id
    δ : NaturalTransformation F (F ∘ F)

  open Functor F

  field
    .assoc     : (δ ∘ʳ F) ∘₁ δ ≡ (F ∘ˡ δ) ∘₁ δ
    .identityˡ : (F ∘ˡ ε) ∘₁ δ ≡ idN
    .identityʳ : (ε ∘ʳ F) ∘₁ δ ≡ idN
