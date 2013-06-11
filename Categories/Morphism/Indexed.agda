{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Support.Equivalence

module Categories.Morphism.Indexed {o a c} (C : Category o a) (B : Set c) where

open import Level using (_⊔_)
open import Data.Product as P using (_,_; _×_)
open import Function as F using () renaming (_∘_ to _⋆_; _∘′_ to _⋆′_)
open import Relation.Binary as B using ()
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import Categories.Support.PropositionalEquality
open import Categories.Operations

import Categories.Object.Indexed as IxOb
open IxOb C B
open Category C
open Heterogeneous C

Fan : Obj → Dust → Set _
Fan X Ys = ∀ b → X ⇒ (Ys ! b)

_⇒∗_ = Fan

Plume : Dust → Obj → Set _
Plume Xs Y = ∀ b → (Xs ! b) ⇒ Y

_∗⇒_ = Plume

Dance : Dust → Dust → Set _
Dance Xs Ys = ∀ b → (Xs ! b) ⇒ (Ys ! b)

_∗⇒∗_ = Dance

_◃_ : ∀ {Xs Y Z} (f : Y ⇒ Z) (g : Xs ∗⇒ Y) → Xs ∗⇒ Z
(f ◃ g) x = f ∘ (g x)

_▹_ : ∀ {X Y Zs} (f : Y ⇒∗ Zs) (g : X ⇒ Y) → X ⇒∗ Zs
(f ▹ g) x = f x ∘ g

_⋊_ : ∀ {Xs Ys Z} (f : Ys ∗⇒ Z) (g : Xs ∗⇒∗ Ys) → Xs ∗⇒ Z
(f ⋊ g) x = f x ∘ g x

_⋉_ : ∀ {X Ys Zs} (f : Ys ∗⇒∗ Zs) (g : X ⇒∗ Ys) → X ⇒∗ Zs
(f ⋉ g) x = f x ∘ g x

_⋈_ : ∀ {Xs Y Zs} (f : Y ⇒∗ Zs) (g : Xs ∗⇒ Y) → Xs ∗⇒∗ Zs
(f ⋈ g) x = f x ∘ g x

_◽_ : ∀ {Xs Ys Zs} (f : Ys ∗⇒∗ Zs) (g : Xs ∗⇒∗ Ys) → Xs ∗⇒∗ Zs
(f ◽ g) x = f x ∘ g x

.assoc-◽⋉ : ∀ {X Ys Zs Ws} {f : Zs ∗⇒∗ Ws} {g : Ys ∗⇒∗ Zs} {h : X ⇒∗ Ys}
          →   _⋉_ {Ys = Ys} {Ws} (_◽_ {Ys} {Zs} {Ws} f g) h
            ≣ _⋉_ {Ys = Zs} {Ws} f (_⋉_ {Ys = Ys} {Zs} g h)
assoc-◽⋉ {f = f} {g} {h} = ≣-ext λ _ → assoc
