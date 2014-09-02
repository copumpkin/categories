{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Diagonal where

open import Data.Product

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Functor.Constant

import Categories.Power as Power

Δ : ∀ {o a} → (C : Category o a) → Functor C (Product C C)
Δ C = EasyFunctor.functor {C = C} {D = Productᵉ C C} record
  { F₀ = λ x → x , x
  ; F₁ = λ f → f , f
  ; identity = refl , refl
  ; homomorphism = refl , refl
  }
  where 
  open Category C
  open Equiv

Δ′ : ∀ {o a} → (I : Set) → (C : Category o a) → Functor C (Power.Exp C I)
Δ′ I C = EasyFunctor.functor {C = C} {D = Power.Expᵉ C I} record 
  { F₀ = λ x _ → x
  ; F₁ = λ f _ → f
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  }
  where
  open Power C
  open Category C
  open Equiv

ΔF : ∀ {o a o₁ a₁} {C : Category o a} (I : Category o₁ a₁) → Functor C (Functors I C)
ΔF {C = C} I = record 
  { F₀ = λ c → Constant c
  ; F₁ = λ f → record { η = λ X → f; commute = λ g → trans C.identityʳ (sym C.identityˡ) }
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  }
 where
   module C = Category C
   open C.Equiv
   module I = Category I
