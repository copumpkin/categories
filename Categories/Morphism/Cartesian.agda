{-# OPTIONS --universe-polymorphism #-}
module Categories.Morphism.Cartesian where

open import Level

open import Categories.Operations
open import Categories.Category
open import Categories.Functor hiding (_≡_)

record CartesianProperties {o₀ a₀} {o₁ a₁} 
                           {E : Category o₀ a₀} {B : Category o₁ a₁} 
                           {p : Functor E B} {e′ e} {φ : E [ e′ , e ]}
                           {e′′ : Category.Obj E} {ψ : E [ e′′ , e ]}
                           {g : B [ Functor.F₀ p e′′ , Functor.F₀ p e′ ]}
                           (pf : Category._≡_ B (Category.compose B (Functor.F₁ p φ) g) (Functor.F₁ p ψ)) : Set (o₀ ⊔ a₀ ⊔ a₁) where
  private module E = Category E
  private module B = Category B
  open B using (Category-composes; _≡_)
  open E using (Category-composes) renaming (_≡_ to _≡E_)
  open Functor p renaming (F₀ to p₀; F₁ to p₁)

  field
    χ        : E [ e′′ , e′ ]
    ψ≡φ∘χ    : ψ ≡E φ ∘ χ
    p₁[χ]≡g  : p₁ χ ≡ g

    χ-unique : (f : E [ e′′ , e′ ]) → ψ ≡E φ ∘ f → p₁ f ≡ g → f ≡E χ


record Cartesian {o₀ a₀} {o₁ a₁} {E : Category o₀ a₀} {B : Category o₁ a₁} (p : Functor E B) {e′ e} (φ : E [ e′ , e ]) : Set (o₀ ⊔ a₀ ⊔ a₁) where
  private module E = Category E
  private module B = Category B
  open B using (Category-composes; _≡_)
  open E using (Category-composes) renaming (_≡_ to _≡E_)
  open Functor p renaming (F₀ to p₀; F₁ to p₁)

  field
    properties : ∀ {e′′} (ψ : E [ e′′ , e ]) (g : B [ p₀ e′′ , p₀ e′ ]) (pf : p₁ φ ∘ g ≡ p₁ ψ) → CartesianProperties {p = p} pf
