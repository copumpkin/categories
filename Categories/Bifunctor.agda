{-# OPTIONS --universe-polymorphism #-}
module Categories.Bifunctor where

open import Level
open import Data.Product using (_,_; swap)

open import Categories.Operations
open import Categories.Category

open import Categories.Functor public
open import Categories.Product

Bifunctor : ∀ {o a} {o′ a′} {o′′ a′′} → Category o a → Category o′ a′ → Category o′′ a′′ → Set (o ⊔ a ⊔ o′ ⊔ a′ ⊔ o′′ ⊔ a′′)
Bifunctor C D E = Functor (Product C D) E

overlap-× : ∀ {o a} {o′₁ a′₁} {o′₂ a′₂} {C : Category o a} {D₁ : Category o′₁ a′₁} {D₂ : Category o′₂ a′₂} (H : Bifunctor D₁ D₂ C) {o″ a″} {E : Category o″ a″} (F : Functor E D₁) (G : Functor E D₂) → Functor E C
overlap-× H F G = H ∘ (F ※ G)

reduce-× : ∀ {o a} {o′₁ a′₁} {o′₂ a′₂} {C : Category o a} {D₁ : Category o′₁ a′₁} {D₂ : Category o′₂ a′₂} (H : Bifunctor D₁ D₂ C) {o″₁ a″₁} {E₁ : Category o″₁ a″₁} (F : Functor E₁ D₁) {o″₂ a″₂} {E₂ : Category o″₂ a″₂} (G : Functor E₂ D₂) → Bifunctor E₁ E₂ C
reduce-× H F G = H ∘ (F ⁂ G)

flip-bifunctor : ∀ {o a} {o′ a′} {o′′ a′′} {C : Category o a} → {D : Category o′ a′} → {E : Category o′′ a′′} → Bifunctor C D E → Bifunctor D C E
flip-bifunctor {C = C} {D = D} {E = E} b = _∘_ b (Swap {C = C} {D = D})
