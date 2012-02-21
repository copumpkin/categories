{-# OPTIONS --universe-polymorphism #-}
module Categories.Graphs where

open import Categories.Category
  hiding (module Heterogeneous)
open import Data.Product
open import Level
open import Relation.Binary
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
  using ()
  renaming (_≡_ to _≣_; refl to ≣-refl)

open import Graphs.Graph
open import Graphs.GraphMorphism

Graphs : ∀ o a → Category (suc (o ⊔ a)) (o ⊔ a)
Graphs o a = record
  { Obj = Graph o a
  ; _⇒_ = GraphMorphism
  ; id = id
  ; _∘_ = _∘_
  ; ASSOC = λ f g h → ≣-refl
  ; IDENTITYˡ = λ f → ≣-refl
  ; IDENTITYʳ = λ f → ≣-refl
  }

Graphsᵉ : ∀ o a → EasyCategory (suc (o ⊔ a)) (o ⊔ a) (o ⊔ a)
Graphsᵉ o a = UNEASY Graphs o a WITH record
  { _≡_     = _≈_
  ; promote = promote
  ; REFL    = λ {_ _ f} → IsEquivalence.refl isEquivalence {f}
  }