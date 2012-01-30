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

Graphs : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Graphs o ℓ e = record
  { Obj       = Obj
  ; _⇒_       = _⇒_
  ; _≡_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; equiv     = isEquivalence
  ; assoc     = λ {A}{B}{C}{D}{f}{g}{h} → assoc {A}{B}{C}{D}{f}{g}{h}
  ; identityˡ = λ {A}{B}{f : A ⇒ B} → IsEquivalence.refl (isEquivalence {A = A}{B}) {x = f}
  ; identityʳ = λ {A}{B}{f : A ⇒ B} → IsEquivalence.refl (isEquivalence {A = A}{B}) {x = f}
  ; ∘-resp-≡  = λ {_}{_}{_}{f}{h}{g}{i} → ∘-resp-≈ {F = f}{h}{g}{i}
  }
  where
    Obj : Set (suc (o ⊔ ℓ ⊔ e))
    Obj = Graph o ℓ e
    
    _⇒_ : Obj → Obj → Set _
    _⇒_ = GraphMorphism
    
    .assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
    assoc {f = f}{g}{h} = (λ x → ≣-refl) , (λ f → refl)
      where open Heterogeneous _
