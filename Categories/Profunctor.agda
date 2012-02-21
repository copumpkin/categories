{-# OPTIONS --universe-polymorphism #-}
module Categories.Profunctor where

open import Level hiding (lift)

open import Categories.Category
open import Categories.Agda
open import Categories.Bifunctor using (Functor; Bifunctor; _∘_)
open import Categories.Functor.Hom
open import Categories.Lan
open import Categories.Yoneda

Profunctor : ∀ {o a} {o′ a′} → Category o a → Category o′ a′ → Set _
Profunctor {a = a} {a′ = a′} C D = Bifunctor (Category.op D) C (Sets (a ⊔ a′))

id : ∀ {o a} → {C : Category o a} → Profunctor C C
id {C = C} = Hom[ C ][-,-]

{-
_∘_ : ∀ {o a} {o′ a′} {o′′ a′′} {C : Category o a} {D : Category o′ a′} {E : Category o′′ a′′} 
    → Profunctor D E → Profunctor C D → Profunctor C E
F ∘ G = {!!}
-}