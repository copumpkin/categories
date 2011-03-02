{-# OPTIONS --universe-polymorphism #-}
module Category where

open import Support


record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where 
  infixr 9 _∘_
  infix  4 _≡_

  field
    Obj : Set o
    Hom : Rel Obj ℓ
    _≡_ : ∀ {A B} → Rel (Hom A B) e

    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

  field
    .assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    .identityˡ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f
    .identityʳ : ∀ {A B} {f : Hom A B} → f ∘ id ≡ f
    .equiv     : ∀ {A B} → IsEquivalence (_≡_ {A} {B})
    .∘-resp-≡  : ∀ {A B C} {f h : Hom B C} {g i : Hom A B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

  .∘-resp-≡ˡ : ∀ {A B C} {f h : Hom B C} {g : Hom A B} → f ≡ h → f ∘ g ≡ h ∘ g
  ∘-resp-≡ˡ pf = ∘-resp-≡ pf (IsEquivalence.refl equiv)

  .∘-resp-≡ʳ : ∀ {A B C} {f h : Hom A B} {g : Hom B C} → f ≡ h → g ∘ f ≡ g ∘ h
  ∘-resp-≡ʳ pf = ∘-resp-≡ (IsEquivalence.refl equiv) pf


  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record 
    { Carrier = Hom A B
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }

  op : Category o ℓ e
  op = record 
    { Obj = Obj
    ; Hom = λ x y → Hom y x
    ; _≡_ = _≡_
    ; _∘_ = λ x y → y ∘ x
    ; id = id
    ; assoc = IsEquivalence.sym equiv assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; equiv = record 
      { refl = IsEquivalence.refl equiv
      ; sym = IsEquivalence.sym equiv
      ; trans = IsEquivalence.trans equiv
      }
    ; ∘-resp-≡ = λ f≡h g≡i → ∘-resp-≡ g≡i f≡h
    }

  CommutativeSquare : ∀ {A B C D} → (f : Hom A B) (g : Hom A C) (h : Hom B D) (i : Hom C D) → Set _
  CommutativeSquare f g h i = h ∘ f ≡ i ∘ g


  .identity-unique : ∀ {o} (f : Hom o o) 
                   → (∀ g → _≡_ {o} (f ∘ g) g) → (∀ g → g ∘ f ≡ g)
                   → f ≡ id
  identity-unique f f∘g≡g g∘f≡g = trans (sym identityˡ) (g∘f≡g id)
    where open IsEquivalence equiv








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