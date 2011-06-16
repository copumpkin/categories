{-# OPTIONS --universe-polymorphism #-}
module Categories.2-Category where

open import Level

open import Categories.Category
open import Categories.Categories
open import Categories.Object.Terminal
open import Categories.Terminal
open import Categories.Functor using (Functor)
open import Categories.Bifunctor using (Bifunctor)

record 2-Category (o′ o ℓ e : Level) : Set (suc (o′ ⊔ o ⊔ ℓ ⊔ e)) where
  open Terminal (Categories o ℓ e) (One {o} {ℓ} {e})
  field
    Obj : Set o′
    C[_,_] : (A B : Obj) → Category o ℓ e
    id : {A : Obj} → Functor ⊤ C[ A , A ]
    _∘₀_ : {A B C : Obj} → Bifunctor C[ B , C ] C[ A , B ] C[ A , C ]

  -- The laws will be easier to state once we have monoidal categories