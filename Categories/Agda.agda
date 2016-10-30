{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda where

open import Level
import Relation.Binary
import Function.Equality

import Categories.Support.Equivalence
import Categories.Support.SetoidFunctions

open import Categories.Support.PropositionalEquality
open import Categories.Category
open import Categories.Functor using (Functor)

Sets : ∀ o → Category _ _ _
Sets o = record
  { Obj = Set o
  ; _⇒_ = λ d c → d → c
  ; _≡_ = λ f g → ∀ {x} → f x ≣ g x

  ; _∘_ = λ f g x → f (g x)
  ; id = λ x → x

  ; assoc = ≣-refl
  ; identityˡ = ≣-refl
  ; identityʳ = ≣-refl
  ; equiv = record { refl = ≣-refl; sym = s; trans = t }
  ; ∘-resp-≡ = ∘-resp-≡′
  }
  where
  s : {A B : Set o} → {i j : A → B} → ({x : A} → i x ≣ j x) → {x : A} → j x ≣ i x
  s f {x} rewrite f {x} = ≣-refl

  t : {A B : Set o} {i j k : A → B} → ({x : A} → i x ≣ j x) → ({x : A} → j x ≣ k x) → {x : A} → i x ≣ k x
  t f g {x} rewrite f {x} | g {x} = ≣-refl

  ∘-resp-≡′ : {A B C : Set o} {f h : B → C} {g i : A → B} →
             (∀ {x} → f x ≣ h x) →
             (∀ {x} → g x ≣ i x) → 
             (∀ {x} → f (g x) ≣ h (i x))
  ∘-resp-≡′ {g = g} f≡h g≡i {x} rewrite f≡h {g x} | g≡i {x} = ≣-refl

-- use standard library setoids here, not our special irrelevant ones
Setoids : ∀ c ℓ → Category (suc (ℓ ⊔ c)) (ℓ ⊔ c) (ℓ ⊔ c)
Setoids c ℓ = record
  { Obj = Setoid c ℓ
  ; _⇒_ = _⟶_
  ; _≡_ = λ {X} {Y} → _≡′_ {X} {Y}
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = λ {_} {_} {_} {D} → Setoid.refl D
  ; identityˡ = λ {_} {B} → Setoid.refl B
  ; identityʳ = λ {_} {B} → Setoid.refl B
  ; equiv = λ {A} {B} → record 
    { refl = Setoid.refl B
    ; sym = λ f → Setoid.sym B f
    ; trans = λ f g → Setoid.trans B f g
    }
  ; ∘-resp-≡ = λ {A} {B} {C} {f} {h} {g} {i} → ∘-resp-≡′ {A} {B} {C} {f} {h} {g} {i}
  }
  where
  infix  4 _≡′_
  open Function.Equality using (_⟨$⟩_; cong; _⟶_) renaming (_∘_ to _∘′_; id to id′)
  open Relation.Binary using (Setoid; module Setoid; Rel)

  _≡′_ : ∀ {X Y} → Rel (X ⟶ Y) _
  _≡′_ {X} {Y} f g = ∀ {x} → Setoid._≈_ Y (f ⟨$⟩ x) (g ⟨$⟩ x)

  .∘-resp-≡′ : ∀ {A B C} {f h : B ⟶ C} {g i : A ⟶ B} → f ≡′ h → g ≡′ i → f ∘′ g ≡′ h ∘′ i
  ∘-resp-≡′ {C = C} {h = h} f≡h g≡i {x} = Setoid.trans C f≡h (cong h g≡i)

-- setoids with irrelevant equality
ISetoids : ∀ c ℓ → Category (suc (ℓ ⊔ c)) (ℓ ⊔ c) (ℓ ⊔ c)
ISetoids c ℓ = record
  { Obj = Setoid c ℓ
  ; _⇒_ = _⟶_
  ; _≡_ = λ {A B} → Setoid._≈_ (A ⇨ B)
  ; _∘_ = _∙_
  ; id = id′
  ; assoc = λ {A B C D} {f g h} →
                cong (h ∙ g ∙ f)
  ; identityˡ = λ {A B f} → cong f
  ; identityʳ = λ {A B f} → cong f
  ; equiv = λ {A B} → Setoid.isEquivalence (A ⇨ B)
  ; ∘-resp-≡ = λ f≡h g≡i x≡y → f≡h (g≡i x≡y)
  }
  where
  open Relation.Binary using (Rel)
  open Categories.Support.Equivalence
  open Categories.Support.SetoidFunctions renaming (id to id′)


Lift-IS : ∀ {c ℓ} a b → Functor (ISetoids c ℓ) (ISetoids (c ⊔ a) (ℓ ⊔ b))
Lift-IS {c} {ℓ} a b = record {
                   F₀ = Lift-setoid {c} {ℓ} {a} {b};
                   F₁ = λ f → record { _⟨$⟩_ = λ x → lift (f ⟨$⟩ (lower x)); cong = λ eq → lift (cong f (lower eq)) };
                   identity = λ x → x;
                   homomorphism = λ {_} {_} {_} {f} {g} eq → lift (cong g (cong f (lower eq)));
                   F-resp-≡ = λ eq₀ eq₁ → lift (eq₀ (lower eq₁)) }
  where
    open import Categories.Support.Equivalence
    open Categories.Support.SetoidFunctions renaming (id to id′)

