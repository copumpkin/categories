{-# OPTIONS --universe-polymorphism #-}
module Categories.Quivers.Underlying where

open import Categories.Support.PropositionalEquality

open import Categories.Category
  hiding (module Heterogeneous)
open import Categories.Categories
open import Categories.Quivers
open import Categories.Functor
  using (Functor; module Functor; ≡⇒≣)
  renaming (id to idF; _≡_ to _≡F_)
open import Data.Product
open import Graphs.Quiver
open import Graphs.Quiver.Morphism

Underlying₀ : ∀ {o a} → Category o a → Quiver o a
Underlying₀ C = record
  { Obj   = Obj
  ; _⇒_   = _⇒_
  } where open Category C

Underlying₁ : ∀ {o₁ a₁ o₂ a₂}
  {X : Category o₁ a₁}
  {Y : Category o₂ a₂}
  → Functor X Y
  → QuiverMorphism (Underlying₀ X) (Underlying₀ Y)
Underlying₁ G = record
  { F₀        = G₀
  ; F₁        = G₁
  }
  where
  open Functor G renaming (F₀ to G₀; F₁ to G₁)

Underlying : ∀ {o a} → Functor (Categories o a) (Quivers o a)
Underlying {o}{a} = record
  { F₀            = Underlying₀ 
  ; F₁            = Underlying₁
  ; identity      = ≣-refl
  ; homomorphism  = ≣-refl
  }
