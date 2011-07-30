{-# OPTIONS --universe-polymorphism #-}
module Categories.Bifunctor where

open import Level
open import Data.Product using (_,_; swap)

open import Categories.Category

open import Categories.Functor public
open import Categories.Product

Bifunctor : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} → Category o ℓ e → Category o′ ℓ′ e′ → Category o′′ ℓ′′ e′′ → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o′′ ⊔ ℓ′′ ⊔ e′′)
Bifunctor C D E = Functor (Product C D) E

overlap-× : ∀ {o ℓ e} {o′₁ ℓ′₁ e′₁} {o′₂ ℓ′₂ e′₂} {C : Category o ℓ e} {D₁ : Category o′₁ ℓ′₁ e′₁} {D₂ : Category o′₂ ℓ′₂ e′₂} (H : Bifunctor D₁ D₂ C) {o″ ℓ″ e″} {E : Category o″ ℓ″ e″} (F : Functor E D₁) (G : Functor E D₂) → Functor E C
overlap-× H F G = H ∘ (F ※ G)

reduce-× : ∀ {o ℓ e} {o′₁ ℓ′₁ e′₁} {o′₂ ℓ′₂ e′₂} {C : Category o ℓ e} {D₁ : Category o′₁ ℓ′₁ e′₁} {D₂ : Category o′₂ ℓ′₂ e′₂} (H : Bifunctor D₁ D₂ C) {o″₁ ℓ″₁ e″₁} {E₁ : Category o″₁ ℓ″₁ e″₁} (F : Functor E₁ D₁) {o″₂ ℓ″₂ e″₂} {E₂ : Category o″₂ ℓ″₂ e″₂} (G : Functor E₂ D₂) → Bifunctor E₁ E₂ C
reduce-× H F G = H ∘ (F ⁂ G)

flip-bifunctor : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} → {D : Category o′ ℓ′ e′} → {E : Category o′′ ℓ′′ e′′} → Bifunctor C D E → Bifunctor D C E
flip-bifunctor {C = C} {D = D} {E = E} b = _∘_ b (Swap {C = C} {D = D})
