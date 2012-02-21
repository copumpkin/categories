{-# OPTIONS --universe-polymorphism #-}
module Categories.Discrete where

open import Level
open import Data.Unit using (⊤)
open import Function using (flip)

open import Categories.Category
open import Categories.Support.PropositionalEquality

Discreteᵉ : ∀ {o} (A : Set o) → EasyCategory o o zero
Discreteᵉ A = record 
  { Obj = A
  ; _⇒_ = _≣_
  ; _≡_ = λ _ _ → ⊤
  ; _∘_ = flip ≣-trans
  ; id = ≣-refl
  ; assoc = _
  ; identityˡ = _
  ; identityʳ = _
  ; promote = λ f g _ → ≣-irrelevance f g
  ; REFL = _
  }

Discrete : ∀ {o} (A : Set o) → Category o o
Discrete A = EASY Discreteᵉ A
