{-# OPTIONS --universe-polymorphism #-}
module Categories.Quivers where

open import Categories.Category
  hiding (module Heterogeneous)
open import Data.Product
open import Level
open import Relation.Binary
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
  using ()
  renaming (_≡_ to _≣_; refl to ≣-refl)

open import Graphs.Quiver
open import Graphs.Quiver.Morphism

Quivers : ∀ o a → Category (suc (o ⊔ a)) (o ⊔ a)
Quivers o a = record
  { Obj = Quiver o a
  ; _⇒_ = QuiverMorphism
  ; id = id
  ; compose = compose
  ; ASSOC = λ f g h → ≣-refl
  ; IDENTITYˡ = λ f → ≣-refl
  ; IDENTITYʳ = λ f → ≣-refl
  }

Quiversᵉ : ∀ o a → EasyCategory (suc (o ⊔ a)) (o ⊔ a) (o ⊔ a)
Quiversᵉ o a = UNEASY Quivers o a WITH record
  { _≡_     = _≈_
  ; promote = promote
  ; REFL    = λ {_ _ f} → IsEquivalence.refl isEquivalence {f}
  }
