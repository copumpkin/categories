{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Diagonal where

open import Data.Product

open import Categories.Category
open import Categories.Functor
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Functor.Constant

import Categories.Power as Power

Δ : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Product C C)
Δ C = record
  { F₀ = λ x → x , x
  ; F₁ = λ f → f , f
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≡ = λ x → x , x
  }
  where 
  open Category C
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
  open Category C
  open Equiv

ΔF : ∀ {o ℓ e o₁ ℓ₁ e₁} {C : Category o ℓ e} (I : Category o₁ ℓ₁ e₁) → Functor C (Functors I C)
ΔF {C = C} I = record 
  { F₀ = λ c → Constant c
  ; F₁ = λ f → record { η = λ X → f; commute = λ g → trans C.identityʳ (sym C.identityˡ) }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≡ = λ x → x
  }
 where
   module C = Category C
   open C.Equiv
   module I = Category I
