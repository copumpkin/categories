{-# OPTIONS --universe-polymorphism #-}
module Categories.Comma.Functors where

open import Categories.Category
open import Categories.Functor
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; zip; map)
open import Level
open import Relation.Binary using (Rel)
open import Categories.Support.EqReasoning

open import Categories.Comma
open import Categories.Product

πComma :
  ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
    → {A : Category o₁ ℓ₁ e₁}
    → {B : Category o₂ ℓ₂ e₂}
    → {C : Category o₃ ℓ₃ e₃}
    → (S : Functor B C) (T : Functor A C)
    → Functor (S ↓ T) (Product B A)
πComma {A = A} {B} {C} S T =
  record
    { F₀ = F₀′
    ; F₁ = F₁′
    ; identity = B×A.Equiv.refl
    ; homomorphism = B×A.Equiv.refl
    ; F-resp-≡ = λ pf → pf
    }
  where
    module S↓T = Category (S ↓ T)
    module B×A = Category (Product B A)
    open Comma S T using (_,_[_]) renaming (_,_,_ to ⟨_,_,_⟩)

    F₀′ : S↓T.Obj → B×A.Obj
    F₀′ ⟨ α , β , f ⟩ = α , β

    F₁′ : ∀ {X Y} → (S ↓ T) [ X , Y ] → Product B A [ F₀′ X , F₀′ Y ]
    F₁′ (g , h [ commutes ]) = g , h
