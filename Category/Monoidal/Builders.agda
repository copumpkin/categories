{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Builders where

open import Support hiding (_×_)
open import Category

open import Category.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Category.NaturalIsomorphism
open import Category.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)
open import Category.Functor.Constant

module MonoidalHelperBuilders {o ℓ e} (C : Category o ℓ e) (⊗ : Bifunctor C C C) (id : Category.Obj C) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ)

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  open import Category.Product

  id₁ : Endofunctor C
  id₁ = idF {C = C}

  id₂ : NaturalTransformation id₁ id₁
  id₂ = idⁿ {F = id₁}

  FunctorToC : (C′ : Category o ℓ e) → Set (o ⊔ ℓ ⊔ e)
  FunctorToC C′ = Functor C′ C

  infix 2 _⟨⊗⟩_
  _⟨⊗⟩_ : {C₁ : Category o ℓ e} {C₂ : Category o ℓ e} → (F : FunctorToC C₁) → (G : FunctorToC C₂) → FunctorToC (Product C₁ C₂)
  F ⟨⊗⟩ G = ⊗ ∘F (F ⁂ G)

  Triendo : Set (o ⊔ ℓ ⊔ e)
  Triendo = Functor (Product (Product C C) C) C

  Tetraendo : Set (o ⊔ ℓ ⊔ e)
  Tetraendo = Functor (Product (Product (Product C C) C) C) C

  infix 2 _⟨⊗⟩ⁿ_
  _⟨⊗⟩ⁿ_ : {C₁ C₂ : Category o ℓ e} {F₁ G₁ : FunctorToC C₁} {F₂ G₂ : FunctorToC C₂} (η₁ : NaturalTransformation F₁ G₁) (η₂ : NaturalTransformation F₂ G₂) → NaturalTransformation (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂)
  η₁ ⟨⊗⟩ⁿ η₂ = ⊗ ∘ˡ (η₁ ⁂ⁿ η₂)
