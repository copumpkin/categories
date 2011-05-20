{-# OPTIONS --universe-polymorphism #-}
module Category where

open import Support

record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where 
  infixr 9 _∘_
  infix  4 _≡_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    _≡_ : ∀ {A B} → Rel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    .assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    .identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    .identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    .equiv     : ∀ {A B} → IsEquivalence (_≡_ {A} {B})
    .∘-resp-≡  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

  module Equiv where
    .refl : ∀ {A B} → {f : A ⇒ B} → f ≡ f
    refl = IsEquivalence.refl equiv

    .sym : ∀ {A B} → {f g : A ⇒ B} → f ≡ g → g ≡ f
    sym = IsEquivalence.sym equiv

    .trans : ∀ {A B} → {f g h : A ⇒ B} → f ≡ g → g ≡ h → f ≡ h
    trans = IsEquivalence.trans equiv

    .prop : ∀ {A B} {f g : A ⇒ B} → f ≣ g → f ≡ g
    prop ≣-refl = refl

  private open Equiv

  .∘-resp-≡ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≡ h → f ∘ g ≡ h ∘ g
  ∘-resp-≡ˡ pf = ∘-resp-≡ pf refl

  .∘-resp-≡ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≡ h → g ∘ f ≡ g ∘ h
  ∘-resp-≡ʳ pf = ∘-resp-≡ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record 
    { Carrier = A ⇒ B
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }

  op : Category o ℓ e
  op = record 
    { Obj = Obj
    ; _⇒_ = flip _⇒_
    ; _≡_ = _≡_
    ; _∘_ = flip _∘_
    ; id = id
    ; assoc = sym assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; equiv = record 
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    ; ∘-resp-≡ = flip ∘-resp-≡
    }

  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≡ i ∘ g


  .id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≡ g) → f ≡ id
  id-unique g∘f≡g = trans (sym identityˡ) (g∘f≡g id)

  .id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ id ∘ f
  id-comm = trans identityʳ (sym identityˡ)

_[_,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_≡_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≡_] = Category._≡_

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

{-

module PreorderCategory {o ℓ e} (P : Preorder o e ℓ) where
  open Preorder P

  PreorderCategory : Category o ℓ zero
  PreorderCategory = record 
    { Obj = Carrier
    ; Hom = _∼_
    ; _≡_ = λ _ _ → ⊤
    ; _∘_ = λ x y → Preorder.trans P y x
    ; id = Preorder.refl P
    ; ∘-assoc = λ _ _ _ → _
    ; identityˡ = λ _ → _
    ; identityʳ = λ _ → _
    ; ≡-equiv = record 
      { refl = _
      ; sym = λ _ → _
      ; trans = λ _ _ → _
      }
    ; ∘-resp-≡ = {!!}
    }

  open Category PreorderCategory
  open Constructs PreorderCategory

  -- FIXME: the univ parameter is too restrictive. It should really take the other two arrows as parameters.
  PreorderPullback : ∀ {a b c} → ∀ x → x ∼ a → x ∼ b → (∀ y → y ∼ x) → PullbackBuilder a b c
  PreorderPullback {a} {b} {c} x pf₁ pf₂ univ f g = record 
    { P = x
    ; p₁ = pf₁
    ; p₂ = pf₂
    ; commutes = _
    ; universal = λ _ _ _ → univ _
    ; universal-unique = λ _ _ _ → _
    ; p₁∘universal≡q₁ = _
    ; p₂∘universal≡q₂ = _
    }
-}