{-# OPTIONS --universe-polymorphism #-}
module Categories.Bifunctor.NaturalTransformation where

open import Level

open import Categories.Category
open import Categories.Bifunctor
open import Categories.Product

open import Categories.NaturalTransformation public

-- just for completeness ...
BiNaturalTransformation : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′} → Bifunctor C D E → Bifunctor C D E → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o′′ ⊔ ℓ′′ ⊔ e′′)
BiNaturalTransformation F G = NaturalTransformation F G

reduceN-× : ∀ {o ℓ e} {o′₁ ℓ′₁ e′₁} {o′₂ ℓ′₂ e′₂} {C : Category o ℓ e} {D₁ : Category o′₁ ℓ′₁ e′₁} {D₂ : Category o′₂ ℓ′₂ e′₂} (H : Bifunctor D₁ D₂ C) {o″₁ ℓ″₁ e″₁} {E₁ : Category o″₁ ℓ″₁ e″₁} {F F′ : Functor E₁ D₁} (φ : NaturalTransformation F F′) {o″₂ ℓ″₂ e″₂} {E₂ : Category o″₂ ℓ″₂ e″₂} {G G′ : Functor E₂ D₂} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce-× {D₁ = D₁} {D₂ = D₂} H F G) (reduce-× {D₁ = D₁} {D₂ = D₂} H F′ G′)
reduceN-× H φ γ = H ∘ˡ (φ ⁂ⁿ γ)

overlapN-× : ∀ {o ℓ e} {o′₁ ℓ′₁ e′₁} {o′₂ ℓ′₂ e′₂} {C : Category o ℓ e} {D₁ : Category o′₁ ℓ′₁ e′₁} {D₂ : Category o′₂ ℓ′₂ e′₂} (H : Bifunctor D₁ D₂ C) {o″ ℓ″ e″} {E : Category o″ ℓ″ e″} {F F′ : Functor E D₁} (φ : NaturalTransformation F F′) {G G′ : Functor E D₂} (γ : NaturalTransformation G G′) → NaturalTransformation (overlap-× {D₁ = D₁} {D₂ = D₂} H F G) (overlap-× {D₁ = D₁} {D₂ = D₂} H F′ G′)
overlapN-× H φ γ = H ∘ˡ (φ ※ⁿ γ)