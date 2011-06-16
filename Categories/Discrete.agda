{-# OPTIONS --universe-polymorphism #-}
module Categories.Discrete where

open import Level
open import Data.Unit using (⊤)
open import Function using (flip)

open import Categories.Category
open import Categories.Support.PropositionalEquality

Discrete : ∀ {o} (A : Set o) → Category o o zero
Discrete A = record 
  { Obj = A
  ; _⇒_ = _≣_
  ; _≡_ = λ _ _ → ⊤
  ; _∘_ = flip ≣-trans
  ; id = ≣-refl
  ; assoc = _
  ; identityˡ = _
  ; identityʳ = _
  ; equiv = _
  ; ∘-resp-≡ = _
  }