{-# OPTIONS --universe-polymorphism #-}
module Category.Profunctor where

open import Support
open import Category
open import Category.Agda
open import Category.Bifunctor using (Bifunctor)
open import Category.Functor.Hom

Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))

id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
id {C = C} = Hom[-,-] {C = C}