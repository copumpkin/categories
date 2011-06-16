{-# OPTIONS --universe-polymorphism #-}
module Categories.Morphism.Cartesian where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; _∘_)

record CartesianProperties {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} 
                           {E : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} 
                           {p : Functor E B} {e′ e} {φ : E [ e′ , e ]}
                           {e′′ : Category.Obj E} {ψ : E [ e′′ , e ]}
                           {g : B [ Functor.F₀ p e′′ , Functor.F₀ p e′ ]}
                           (pf : Category._≡_ B (Category._∘_ B (Functor.F₁ p φ) g) (Functor.F₁ p ψ)) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ ℓ₁ ⊔ e₁) where
  private module E = Category E
  private module B = Category B
  open B using (_∘_; _≡_)
  open E using () renaming (_∘_ to _∘E_; _≡_ to _≡E_)
  open Functor p renaming (F₀ to p₀; F₁ to p₁)

  field
    χ        : E [ e′′ , e′ ]
    ψ≡φ∘χ    : ψ ≡E φ ∘E χ
    p₁[χ]≡g  : p₁ χ ≡ g

    χ-unique : (f : E [ e′′ , e′ ]) → ψ ≡E φ ∘E f → p₁ f ≡ g → f ≡E χ


record Cartesian {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {E : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} (p : Functor E B) {e′ e} (φ : E [ e′ , e ]) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ ℓ₁ ⊔ e₁) where
  private module E = Category E
  private module B = Category B
  open B using (_∘_; _≡_)
  open E using () renaming (_∘_ to _∘E_; _≡_ to _≡E_)
  open Functor p renaming (F₀ to p₀; F₁ to p₁)

  field
    properties : ∀ {e′′} (ψ : E [ e′′ , e ]) (g : B [ p₀ e′′ , p₀ e′ ]) (pf : p₁ φ ∘ g ≡ p₁ ψ) → CartesianProperties {p = p} pf
