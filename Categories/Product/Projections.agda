{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Categories.Category
open import Categories.Product

module Categories.Product.Projections 
    {o a o′ a′}
    (C : Category o a)
    (D : Category o′ a′)
    where

open import Categories.Functor
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)

∏₁ : Functor (Product C D) C
∏₁ = record 
    { F₀            = proj₁
    ; F₁            = proj₁
    ; identity      = refl
    ; homomorphism  = refl
    } where
        open Category.Equiv C


∏₂ : Functor (Product C D) D
∏₂ = record 
    { F₀            = proj₂
    ; F₁            = proj₂
    ; identity      = refl
    ; homomorphism  = refl
    } where
        open Category.Equiv D
