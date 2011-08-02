{-# OPTIONS --universe-polymorphism #-}
module Categories.DinaturalTransformation where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Bifunctor hiding (equiv) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)

record DinaturalTransformation {o ℓ e o′ ℓ′ e′}
                               {C : Category o ℓ e}
                               {D : Category o′ ℓ′ e′}
                               (F G : Bifunctor (Category.op C) C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  module C = Category C
  module D = Category D
  open Functor F
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  open D
  field
    α : (c : C.Obj) → D [ F₀ (c , c) , G₀ (c , c) ]

    .commute : ∀ {c c′} (f : C [ c , c′ ]) → G₁ (f , C.id) ∘ α c′ ∘ F₁ ( C.id , f ) ≡ G₁ ( C.id , f ) ∘ α c ∘ F₁ ( f , C.id )