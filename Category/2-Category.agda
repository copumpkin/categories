{-# OPTIONS --universe-polymorphism #-}
module Category.2-Category where

open import Support hiding (⊤)
open import Category
open import Category.Categories
open import Category.Object.Terminal
open import Category.Terminal
open import Category.Functor using (Functor)
open import Category.Bifunctor using (Bifunctor)

record 2-Category (o′ o ℓ e : Level) : Set (suc (o′ ⊔ o ⊔ ℓ ⊔ e)) where
  open Terminal (Categories o ℓ e) (One {o} {ℓ} {e})
  field
    Obj : Set o′
    C[_,_] : (A B : Obj) → Category o ℓ e
    id : {A : Obj} → Functor ⊤ C[ A , A ]
    _∘₀_ : {A B C : Obj} → Bifunctor C[ B , C ] C[ A , B ] C[ A , C ]

  -- The laws will be easier to state once we have monoidal categories