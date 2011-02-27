{-# OPTIONS --universe-polymorphism #-}
module Category.Bifunctor where

open import Support hiding (_×_)
open import Category

open import Category.Functor public
open import Category.Product

Bifunctor : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} → Category o ℓ e → Category o′ ℓ′ e′ → Category o′′ ℓ′′ e′′ → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o′′ ⊔ ℓ′′ ⊔ e′′)
Bifunctor C D E = Functor (Product C D) E