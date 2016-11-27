{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category
open import Categories.Object.Products
open import Categories.Object.Terminal
open import Level

module Categories.Object.Terminal.Exponentiating {o ℓ e : Level}
    (C : Category o ℓ e)
    (P : Products C) where

open Category C
open Products P
open Terminal terminal

open import Categories.Object.Exponentiating
import Categories.Object.Terminal.Exponentials

open Categories.Object.Terminal.Exponentials C terminal

⊤-exponentiating : Exponentiating C binary ⊤
⊤-exponentiating = record
  { exponential = λ {X : Obj} → [⊤↑ X ]-exponential
  }
