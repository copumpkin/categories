{-# OPTIONS --universe-polymorphism #-}

open import Level

module Categories.Terminal {o a : Level} where

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor
open import Categories.Categories
import Categories.Object.Terminal as Terminal

open Terminal (Categories o a)

record Unit {x : _} : Set x where
  constructor unit

-- I can probably use Discrete here once we get universe cumulativity in Agda
One : Terminal
One = record 
  { ⊤ = my-⊤
  ; ! = my-!
  ; !-unique = λ F → promote my-! F (λ _ → Heterogeneous.≡⇒∼ ≣-refl)
  }
  where
  unit-unique : ∀ {ℓ} {f g : Unit {ℓ}} → unit ≣ f
  unit-unique {f = unit} {unit} = ≣-refl

  my-⊤ = record 
    { Obj = Unit
    ; _⇒_ = λ _ _ → Unit
    ; _∘_ = λ _ _ → unit
    ; id = unit
    ; ASSOC = λ f g h → ≣-refl
    ; IDENTITYˡ = λ f → unit-unique
    ; IDENTITYʳ = λ f → unit-unique
    }

  my-! : ∀ {A} → Functor A my-⊤
  my-! = record
    { F₀ = λ _ → unit
    ; F₁ = λ _ → unit
    ; identity = ≣-refl
    ; homomorphism = ≣-refl
    }
