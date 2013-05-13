{-# OPTIONS --universe-polymorphism #-}
module Graphs.Quiver where

open import Level
open import Categories.Support.Equivalence
open import Relation.Binary
  using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality as PropEq
  using ()
  renaming (_≡_ to _≣_)

record Quiver (o a : Level) : Set (suc (o ⊔ a)) where
  field
    Obj     : Set o
    _⇒_     : Obj → Obj → Set a

open Quiver public using () renaming (_⇒_ to _[_,_])

module Heterogeneous {o a} (G : Quiver o a) where
  open Quiver G

  data _~_ {A B} (f : A ⇒ B) : ∀ {X Y} → (X ⇒ Y) → Set (a) where
    ≈⇒~ : {g : A ⇒ B} → f ≣ g → f ~ g

  refl : ∀ {A B} {f : A ⇒ B} → f ~ f
  refl = ≈⇒~ PropEq.refl

  sym : ∀ {A B} {f : A ⇒ B} {D E} {g : D ⇒ E} → f ~ g → g ~ f
  sym (≈⇒~ f≈g) = ≈⇒~ (PropEq.sym f≈g)

  trans : ∀ {A B} {f : A ⇒ B} 
            {D E} {g : D ⇒ E}
            {F G} {h : F ⇒ G}
          → f ~ g → g ~ h → f ~ h
  trans (≈⇒~ f≈g) (≈⇒~ g≈h) = ≈⇒~ (PropEq.trans f≈g g≈h)

  ~⇒≈ : ∀ {A B} {f g : A ⇒ B} → f ~ g → f ≣ g
  ~⇒≈ (≈⇒~ f≈g) = f≈g

_[_~_] : ∀ {o a} (G : Quiver o a) {A B} (f : G [ A , B ]) {X Y} (g : G [ X , Y ]) → Set (a)
G [ f ~ g ] = Heterogeneous._~_ G f g