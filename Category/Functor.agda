{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public

open import Category.NaturalIsomorphism

infix  4 _≡_

_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Rel (Functor C D) _
_≡_ = NaturalIsomorphism

.assoc : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {o′′′ ℓ′′′ e′′′} 
           {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o′′ ℓ′′ e′′} {D : Category o′′′ ℓ′′′ e′′′}
       → {F : Functor A B} → {G : Functor B C} → {H : Functor C D} → (H ∘ G) ∘ F ≡ H ∘ (G ∘ F)
assoc {A = A} {F = F} {G} {H} = record 
  { F⇒G = record 
    { η = λ _ → H₁ (G₁ (F₁ A.id))
    ; commute = λ f → {!!}
    }
  ; F⇐G = record 
    { η = λ _ → H₁ (G₁ (F₁ A.id))
    ; commute = λ f → {!!}
    }
  ; iso = λ X → record 
    { isoˡ = {!!}
    ; isoʳ = {!!}
    }
  }
  where
  module A = Category.Category A
  module F = Functor F
  module G = Functor G
  module H = Functor H
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)
  open H renaming (F₀ to H₀; F₁ to H₁)