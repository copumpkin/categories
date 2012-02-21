{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Support.Equivalence

module Categories.Object.Indexed {o a c q} (C : Category o a) (B : Setoid c q) where

open import Categories.Support.SetoidFunctions
open Category C
open _⟶_ public using () renaming (cong to cong₀; _⟨$⟩_ to _!_)

Objoid = set→setoid Obj

Dust = B ⟶ Objoid

dust-setoid = B ⇨ Objoid