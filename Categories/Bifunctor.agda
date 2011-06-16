{-# OPTIONS --universe-polymorphism #-}
module Categories.Bifunctor where

open import Level

open import Categories.Category

open import Categories.Functor public
open import Categories.Product

Bifunctor : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} → Category o ℓ e → Category o′ ℓ′ e′ → Category o′′ ℓ′′ e′′ → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o′′ ⊔ ℓ′′ ⊔ e′′)
Bifunctor C D E = Functor (Product C D) E