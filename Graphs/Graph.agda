{-# OPTIONS --universe-polymorphism #-}
module Graphs.Graph where

open import Level
open import Categories.Support.Equivalence
open import Relation.Binary
  using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
  using ()
  renaming (_≡_ to _≣_)

record Graph (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    Obj     : Set o
    _↝_     : Obj → Obj → Set ℓ
    _≈_     : {A B : Obj} → Rel (A ↝ B) e
    .equiv  : ∀ {A B : Obj} → IsEquivalence (_≈_ {A}{B})
  
  edge-setoid : ∀ {A B : Obj} → Setoid ℓ e
  edge-setoid {A}{B} = record
    { Carrier       = A ↝ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }
  
  module Equiv {A B : Obj} where
    private
      module e = IsEquivalence
      .q : IsEquivalence _≈_
      q = equiv {A} {B}

    .refl : Reflexive _≈_
    refl = e.refl q
    .trans : Transitive _≈_
    trans = e.trans q
    .sym : Symmetric _≈_
    sym = e.sym q
    .reflexive : _≣_ ⊆ _≈_
    reflexive = e.reflexive q

_[_↝_] : ∀ {o ℓ e} → (G : Graph o ℓ e) → Graph.Obj G → Graph.Obj G → Set ℓ
G [ A ↝ B ] = Graph._↝_ G A B

_[_≈_] : ∀ {o ℓ e} → (G : Graph o ℓ e) → {A B : Graph.Obj G} → Rel (G [ A ↝ B ]) e
G [ f ≈ g ] = Graph._≈_ G f g

module Heterogeneous {o ℓ e} (G : Graph o ℓ e) where
  open Graph G
  open Equiv renaming (refl to refl′; sym to sym′; trans to trans′)

  data _~_ {A B} (f : A ↝ B) : ∀ {X Y} → (X ↝ Y) → Set (ℓ ⊔ e) where
    ≈⇒~ : {g : A ↝ B} → .(f ≈ g) → f ~ g

  refl : ∀ {A B} {f : A ↝ B} → f ~ f
  refl = ≈⇒~ refl′

  sym : ∀ {A B} {f : A ↝ B} {D E} {g : D ↝ E} → f ~ g → g ~ f
  sym (≈⇒~ f≈g) = ≈⇒~ (sym′ f≈g)

  trans : ∀ {A B} {f : A ↝ B} 
             {D E} {g : D ↝ E}
             {F G} {h : F ↝ G}
          → f ~ g → g ~ h → f ~ h
  trans (≈⇒~ f≈g) (≈⇒~ g≈h) = ≈⇒~ (trans′ f≈g g≈h)

_[_~_] : ∀ {o ℓ e} (G : Graph o ℓ e) {A B} (f : G [ A ↝ B ]) {X Y} (g : G [ X ↝ Y ]) → Set (ℓ ⊔ e)
G [ f ~ g ] = Heterogeneous._~_ G f g