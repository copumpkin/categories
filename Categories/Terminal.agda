{-# OPTIONS --universe-polymorphism #-}

open import Level

module Categories.Terminal {o ℓ e : Level} where

open import Categories.Category
open import Categories.Functor
open import Categories.Categories
import Categories.Object.Terminal as Terminal

open Terminal (Categories o ℓ e)

record Unit {x : _} : Set x where
  constructor unit

OneC : Category o ℓ e
OneC = record 
  { Obj = Unit
  ; _⇒_ = λ _ _ → Unit
  ; _≡_ = λ _ _ → Unit
  ; _∘_ = λ _ _ → unit
  ; id = unit
  ; assoc = unit
  ; identityˡ = unit
  ; identityʳ = unit
  ; equiv = record 
    { refl = unit
    ; sym = λ _ → unit
    ; trans = λ _ _ → unit
    }
  ; ∘-resp-≡ = λ _ _ → unit
  }

-- I can probably use Discrete here once we get universe cumulativity in Agda
One : Terminal
One = record 
  { ⊤ = OneC
  ; ! = record
    { F₀ = λ _ → unit
    ; F₁ = λ _ → unit
    ; identity = unit
    ; homomorphism = unit
    ; F-resp-≡ = λ _ → unit
    }
  ; !-unique = λ _ _ → Heterogeneous.≡⇒∼ unit
  }
