{-# OPTIONS --universe-polymorphism #-}

open import Support

module Category.Terminal {o ℓ e} where

open import Category
open import Category.Functor
open import Category.Categories
import Category.Object.Terminal as Terminal

open Terminal (Categories o ℓ e)

-- I can probably use Discrete here once we get universe cumulativity in Agda
One : Terminal
One = record 
  { ⊤ = record 
    { Obj = ⊤
    ; Hom = λ _ _ → ⊤
    ; _≡_ = λ _ _ → ⊤
    ; _∘_ = λ _ _ → tt
    ; id = tt
    ; assoc = tt
    ; identityˡ = tt
    ; identityʳ = tt
    ; equiv = record 
      { refl = tt
      ; sym = λ _ → tt
      ; trans = λ _ _ → tt
      }
    ; ∘-resp-≡ = λ _ _ → tt
    }
  ; ! = record
    { F₀ = λ _ → tt
    ; F₁ = λ _ → tt
    ; identity = tt
    ; homomorphism = tt
    ; F-resp-≡ = λ _ → tt
    }
  ; !-unique = λ _ _ → refl tt
  }