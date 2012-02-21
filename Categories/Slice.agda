{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Slice {o a} (C : Category o a) where

open Category C
open Equiv

open import Level
open import Relation.Binary using (Rel)

open import Categories.Support.PropositionalEquality

record SliceObj (X : Obj) : Set (o ⊔ a) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : Y ⇒ X

record Slice⇒ {A : Obj} (X Y : SliceObj A) : Set (a) where
  constructor slicearr
  module X = SliceObj X
  module Y = SliceObj Y
  field
    {h} : X.Y ⇒ Y.Y
    .triangle : Y.arr ∘ h ≡ X.arr

sliceᵉ : Obj → EasyCategory _ _ _
sliceᵉ x = record 
  { Obj = Obj′
  ; _⇒_ = _⇒′_
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = slicearr identityʳ
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; promote = promote
  ; REFL = ≣-refl
  }
  where
  Obj′ = SliceObj x

  _⇒′_ : Rel Obj′ _
  _⇒′_ = Slice⇒

  infixr 9 _∘′_
  infix  4 _≡′_

  _≡′_ : ∀ {A B} → Rel (A ⇒′ B) _
  slicearr {f} _ ≡′ slicearr {g} _ = f ≡ g

  _∘′_ : ∀ {A B C} → (B ⇒′ C) → (A ⇒′ B) → (A ⇒′ C)
  _∘′_ {sliceobj a⇒x} {sliceobj b⇒x} {sliceobj c⇒x} (slicearr {b⇒c} pf₁) (slicearr {a⇒b} pf₂) = slicearr pf
    where
    .pf : c⇒x ∘ (b⇒c ∘ a⇒b) ≡ a⇒x
    pf = begin
           c⇒x ∘ (b⇒c ∘ a⇒b)
         ↑⟨ assoc ⟩
           (c⇒x ∘ b⇒c) ∘ a⇒b
         ↓⟨ ∘-resp-≡ˡ pf₁ ⟩
           b⇒x ∘ a⇒b
         ↓⟨ pf₂ ⟩
           a⇒x
         ∎
      where 
      open HomReasoning


  .assoc′ : ∀ {A B C D} {f : A ⇒′ B} {g : B ⇒′ C} {h : C ⇒′ D}
         → (h ∘′ g) ∘′ f ≡′ h ∘′ (g ∘′ f)
  assoc′ = assoc

  .promote : ∀ {A B} (f g : A ⇒′ B) → f ≡′ g → f ≣ g
  promote (slicearr _) (slicearr _) ≣-refl = ≣-refl

slice : Obj → Category _ _
slice x = EASY sliceᵉ x
