{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category hiding (module Heterogeneous)

module Categories.Arrow {o a} (C : Category o a) where

open import Level
open import Relation.Binary using (Rel)
open import Data.Product using (_×_; _,_; map; zip; uncurry)

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open Category C
open Category.Equiv C

record ArrowObj : Set (o ⊔ a) where
  constructor arrobj
  field
    {A} : Obj
    {B} : Obj
    arr : A ⇒ B

record Arrow⇒ (X Y : ArrowObj) : Set (a) where
  constructor arrarr
  module X = ArrowObj X
  module Y = ArrowObj Y
  field
    {f} : X.A ⇒ Y.A
    {g} : X.B ⇒ Y.B
    .square : CommutativeSquare X.arr f g Y.arr

arrow : EasyCategory _ _ _
arrow = record 
  { Obj = Obj′
  ; _⇒_ = _⇒′_
  ; _≡_ = _≡′_
  ; compose = _∘′_
  ; id = id′
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; promote = promote
  ; REFL = refl , refl
  }
  where
  Obj′ = ArrowObj

  _⇒′_ : Rel Obj′ _
  _⇒′_ = Arrow⇒

  infixr 9 _∘′_
  infix  4 _≡′_

  _≡′_ : ∀ {A B} → (f g : A ⇒′ B) → Set _
  (arrarr {f} {h} _) ≡′ (arrarr {i} {g} _) = f ≡ i × h ≡ g

  _∘′_ : ∀ {A B C} → (B ⇒′ C) → (A ⇒′ B) → (A ⇒′ C)
  _∘′_ {arrobj x} {arrobj y} {arrobj z} (arrarr {f} {h} pf₁) (arrarr {i} {g} pf₂) = arrarr pf
    where
    .pf : (h ∘ g) ∘ x ≡ z ∘ (f ∘ i)
    pf = begin
           (h ∘ g) ∘ x
         ↓⟨ assoc ⟩
           h ∘ (g ∘ x)
         ↓⟨ ∘-resp-≡ʳ pf₂ ⟩
           h ∘ (y ∘ i)
         ↑⟨ assoc ⟩
           (h ∘ y) ∘ i
         ↓⟨ ∘-resp-≡ˡ pf₁ ⟩
           (z ∘ f) ∘ i
         ↓⟨ assoc ⟩
           z ∘ (f ∘ i)
         ∎
      where 
      open HomReasoning

  id′ : ∀ {A} → A ⇒′ A
  id′ = arrarr (sym id-comm)

  .assoc′ : ∀ {A B C D} {f : A ⇒′ B} {g : B ⇒′ C} {h : C ⇒′ D} → (h ∘′ g) ∘′ f ≡′ h ∘′ (g ∘′ f)
  assoc′ = assoc , assoc

  promote : ∀ {A B} (f g : A ⇒′ B) → f ≡′ g → f ≣ g
  promote (arrarr square) (arrarr square') (≣-refl , ≣-refl) = ≣-refl