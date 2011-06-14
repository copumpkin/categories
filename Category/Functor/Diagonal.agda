{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Diagonal where

open import Support
open import Category
open import Category.Functor hiding (refl)
open import Category.Product

import Category.Power as Power

Δ : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Product C C)
Δ C = record
  { F₀ = λ x → x , x
  ; F₁ = λ f → f , f
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≡ = λ x → x , x
  }
  where 
  open Category.Category C
  open Equiv

Δ′ : ∀ {o ℓ e} → (I : Set) → (C : Category o ℓ e) → Functor C (Power.Exp C I)
Δ′ I C = record 
  { F₀ = λ x _ → x
  ; F₁ = λ f _ → f
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≡ = λ x _ → x
  }
  where
  open Power C
  open Category.Category C
  open Equiv