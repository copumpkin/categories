{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Slice {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level
open import Relation.Binary using (Rel)

record SliceObj (X : Obj) : Set (o ⊔ ℓ) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : Y ⇒ X

record Slice⇒ {A : Obj} (X Y : SliceObj A) : Set (ℓ ⊔ e) where
  constructor slicearr
  module X = SliceObj X
  module Y = SliceObj Y
  field
    {h} : X.Y ⇒ Y.Y
    .triangle : Y.arr ∘ h ≡ X.arr

slice : Obj → Category _ _ _
slice x = record 
  { Obj = Obj′
  ; _⇒_ = _⇒′_
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = slicearr identityʳ
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record 
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} → ∘-resp-≡′ {f = f} {h} {g} {i}
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

  .∘-resp-≡′ : ∀ {A B C} {f h : B ⇒′ C} {g i : A ⇒′ B}
           → f ≡′ h 
           → g ≡′ i 
           → f ∘′ g ≡′ h ∘′ i
  ∘-resp-≡′ f≡h g≡i = ∘-resp-≡ f≡h g≡i
