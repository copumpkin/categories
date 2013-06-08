{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category hiding (module Heterogeneous)
open import Categories.Congruence

module Categories.Arrow {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary using (Rel)
open import Data.Product using (_×_; _,_; map; zip)

open Category C
open Category.Equiv C

record ArrowObj : Set (o ⊔ ℓ) where
  constructor arrobj
  field
    {A} : Obj
    {B} : Obj
    arr : A ⇒ B

record Arrow⇒ (X Y : ArrowObj) : Set (ℓ ⊔ e) where
  constructor arrarr
  module X = ArrowObj X
  module Y = ArrowObj Y
  field
    {f} : X.A ⇒ Y.A
    {g} : X.B ⇒ Y.B
    .square : CommutativeSquare X.arr f g Y.arr

arrow : Category _ _ _
arrow = record 
  { Obj = Obj′
  ; _⇒_ = _⇒′_
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; equiv = record 
    { refl = refl , refl
    ; sym = map sym sym
    ; trans = zip trans trans
    }
  ; ∘-resp-≡ = zip ∘-resp-≡ ∘-resp-≡
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

module Congruent {q} (Q : Congruence C q) where
  open Congruence Q
  open Heterogeneous Q renaming (refl to ⇉-refl; sym to ⇉-sym; trans to ⇉-trans)

  ArrowEq : Rel ArrowObj _
  ArrowEq (arrobj f) (arrobj g) = f ∼ g

  private
    _⇉_ : Rel ArrowObj _
    _⇉_ = ArrowEq

    open Category arrow using () renaming (_≡_ to _≡′_; _∘_ to _∘′_)

    force : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ⇉ X₂) (pfY : Y₁ ⇉ Y₂)
            → (f : Arrow⇒ X₁ Y₁) → Arrow⇒ X₂ Y₂
    force {arrobj h₁} {arrobj h₂} {arrobj k₁} {arrobj k₂}
          (≡⇒∼ sh th ah) (≡⇒∼ sk tk ak) (arrarr {f} {g} square) = arrarr (
      begin
        coerce th tk g ∘ h₂
      ↑⟨ ∘-resp-≡ʳ ah ⟩
        coerce th tk g ∘ coerce sh th h₁
      ↑⟨ coerce-∘ _ _ _ _ _ ⟩
        coerce sh tk (g ∘ h₁)
      ↓⟨ coerce-resp-≡ _ _ square ⟩
        coerce sh tk (k₁ ∘ f)
      ↓⟨ coerce-∘ _ _ _ _ _ ⟩
        coerce sk tk k₁ ∘ coerce sh sk f
      ↓⟨ ∘-resp-≡ˡ ak ⟩
        k₂ ∘ coerce sh sk f
      ∎)
      where open HomReasoning

    .force-resp-≡′ : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ⇉ X₂) (pfY : Y₁ ⇉ Y₂)
                  → {f₁ f₂ : Arrow⇒ X₁ Y₁}
                  → f₁ ≡′ f₂ → force pfX pfY f₁ ≡′ force pfX pfY f₂
    force-resp-≡′ (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (eq₁ , eq₂)
      = coerce-resp-≡ _ _ eq₁ , coerce-resp-≡ _ _ eq₂

    .force-refl : ∀ {X Y} (f : Arrow⇒ X Y) → force ⇉-refl ⇉-refl f ≡′ f
    force-refl f = coerce-refl _ , coerce-refl _

    .force-inv : ∀ {X₁ X₂ Y₁ Y₂} (pfX₁ pfX₂ : X₁ ⇉ X₂) (pfY₁ pfY₂ : Y₁ ⇉ Y₂)
                 → (f : Arrow⇒ X₁ Y₁) → force pfX₁ pfY₁ f ≡′ force pfX₂ pfY₂ f
    force-inv (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) f
      = coerce-invariant _ _ _ _ _ , coerce-invariant _ _ _ _ _

    .force-trans : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} (pfX₁ : X₁ ⇉ X₂) (pfX₂ : X₂ ⇉ X₃)
                                         (pfY₁ : Y₁ ⇉ Y₂) (pfY₂ : Y₂ ⇉ Y₃)
                   → (f : Arrow⇒ X₁ Y₁)
                   →    force (⇉-trans pfX₁ pfX₂) (⇉-trans pfY₁ pfY₂) f
                     ≡′ force pfX₂ pfY₂ (force pfX₁ pfY₁ f)
    force-trans (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) f
      = coerce-trans _ _ _ _ _ , coerce-trans _ _ _ _ _

    .force-∘′ : ∀ {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
                → (pfX : X₁ ⇉ X₂) (pfY : Y₁ ⇉ Y₂) (pfZ : Z₁ ⇉ Z₂)
                → (g : Arrow⇒ Y₁ Z₁) (f : Arrow⇒ X₁ Y₁)
                → force pfX pfZ (g ∘′ f) ≡′ force pfY pfZ g ∘′ force pfX pfY f
    force-∘′ (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) (≡⇒∼ _ _ _) g f
      = coerce-∘ _ _ _ _ _ , coerce-∘ _ _ _ _ _

  arrowQ : Congruence arrow _
  arrowQ = record
    { _≡₀_ = ArrowEq
    ; equiv₀ = record
      { refl = ⇉-refl
      ; sym = ⇉-sym
      ; trans = ⇉-trans
      }
    ; coerce = force
    ; coerce-resp-≡ = force-resp-≡′
    ; coerce-refl = force-refl
    ; coerce-invariant = force-inv
    ; coerce-trans = force-trans
    ; coerce-∘ = force-∘′
    }

open Congruent (TrivialCongruence C) public using () renaming (arrowQ to arrow∼)
