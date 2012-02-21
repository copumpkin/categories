{-# OPTIONS --universe-polymorphism #-}
module Categories.Bifunctor.NaturalTransformation where

open import Level

open import Categories.Category
open import Categories.Bifunctor
open import Categories.Product

open import Categories.NaturalTransformation public

-- just for completeness ...
BiNaturalTransformation : ∀ {o a} {o′ a′} {o′′ a′′} {C : Category o a} {D : Category o′ a′} {E : Category o′′ a′′} → Bifunctor C D E → Bifunctor C D E → Set (o ⊔ a ⊔ o′ ⊔ a′ ⊔ o′′ ⊔ a′′)
BiNaturalTransformation F G = NaturalTransformation F G

reduceN-× : ∀ {o a} {o′₁ a′₁} {o′₂ a′₂} {C : Category o a} {D₁ : Category o′₁ a′₁} {D₂ : Category o′₂ a′₂} (H : Bifunctor D₁ D₂ C) {o″₁ a″₁} {E₁ : Category o″₁ a″₁} {F F′ : Functor E₁ D₁} (φ : NaturalTransformation F F′) {o″₂ a″₂} {E₂ : Category o″₂ a″₂} {G G′ : Functor E₂ D₂} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce-× {D₁ = D₁} {D₂ = D₂} H F G) (reduce-× {D₁ = D₁} {D₂ = D₂} H F′ G′)
reduceN-× H φ γ = H ∘ˡ (φ ⁂ⁿ γ)

overlapN-× : ∀ {o a} {o′₁ a′₁} {o′₂ a′₂} {C : Category o a} {D₁ : Category o′₁ a′₁} {D₂ : Category o′₂ a′₂} (H : Bifunctor D₁ D₂ C) {o″ a″} {E : Category o″ a″} {F F′ : Functor E D₁} (φ : NaturalTransformation F F′) {G G′ : Functor E D₂} (γ : NaturalTransformation G G′) → NaturalTransformation (overlap-× {D₁ = D₁} {D₂ = D₂} H F G) (overlap-× {D₁ = D₁} {D₂ = D₂} H F′ G′)
overlapN-× H φ γ = H ∘ˡ (φ ※ⁿ γ)