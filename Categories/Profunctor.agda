{-# OPTIONS --universe-polymorphism #-}
module Categories.Profunctor where

open import Level hiding (lift)

open import Categories.Category
open import Categories.Agda
open import Categories.Bifunctor using (Functor; Bifunctor; _∘_)
open import Categories.Functor.Hom
open import Categories.Lan
open import Categories.Yoneda

Profunctor : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Set _
Profunctor {ℓ = ℓ} {e} {ℓ′ = ℓ′} {e′} C D = Bifunctor (Category.op D) C (ISetoids (ℓ ⊔ ℓ′) (e ⊔ e′))

id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor C C
id {C = C} = Hom[ C ][-,-]

{-
_∘_ : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′} 
    → Profunctor D E → Profunctor C D → Profunctor C E
F ∘ G = {!!}
-}