{-# OPTIONS --universe-polymorphism #-}
module Category.Discrete where

open import Support
open import Category

Discrete : ∀ {o} (A : Set o) → Category o o zero
Discrete A = record 
  { Obj = A
  ; _⇒_ = _≣_
  ; _≡_ = λ _ _ → ⊤
  ; _∘_ = ≣-trans
  ; id = ≣-refl
  ; assoc = _
  ; identityˡ = _
  ; identityʳ = _
  ; equiv = _
  ; ∘-resp-≡ = _
  }