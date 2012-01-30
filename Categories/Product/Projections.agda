{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Categories.Category
open import Categories.Product

module Categories.Product.Projections 
    {o ℓ e o′ ℓ′ e′}
    (C : Category o ℓ e)
    (D : Category o′ ℓ′ e′)
    where

open import Categories.Functor
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)

∏₁ : Functor (Product C D) C
∏₁ = record 
    { F₀            = proj₁
    ; F₁            = proj₁
    ; identity      = refl
    ; homomorphism  = refl
    ; F-resp-≡      = proj₁
    } where
        open Category.Equiv C


∏₂ : Functor (Product C D) D
∏₂ = record 
    { F₀            = proj₂
    ; F₁            = proj₂
    ; identity      = refl
    ; homomorphism  = refl
    ; F-resp-≡      = proj₂
    } where
        open Category.Equiv D
