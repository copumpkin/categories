{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda where

open import Level
import Relation.Binary
import Function.Equality

import Categories.Support.Equivalence
import Categories.Support.SetoidFunctions

open import Categories.Support.PropositionalEquality
open import Categories.Category
open import Categories.Category.Quotient

Setsᵉ : ∀ o → EasyCategory _ _ _
Setsᵉ o = record
  { Obj = Set o
  ; _⇒_ = λ d c → d → c
  ; _≡_ = λ f g → ∀ {x} → f x ≣ g x

  ; compose = λ f g x → f (g x)
  ; id = λ x → x

  ; assoc = ≣-refl
  ; identityˡ = ≣-refl
  ; identityʳ = ≣-refl
  ; promote = λ f g f≗g → ≣-ext (λ x → f≗g)
  ; REFL = ≣-refl
  }

Sets : ∀ o → Category _ _
Sets o = EASY Setsᵉ o

-- use standard library setoids here, not our special irrelevant ones
SetoidsQ : ∀ c ℓ → QCategory (suc (ℓ ⊔ c)) (ℓ ⊔ c) (ℓ ⊔ c)
SetoidsQ c ℓ = record
  { Obj = Setoid c ℓ
  ; _⇒_ = _⟶_
  ; _≡_ = λ {X} {Y} → _≡′_ {X} {Y}
  ; compose = _∘′_
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
  open Relation.Binary using (Setoid; Rel)

  _≡′_ : ∀ {X Y} → Rel (X ⟶ Y) _
  _≡′_ {X} {Y} f g = ∀ {x} → Setoid._≈_ Y (f ⟨$⟩ x) (g ⟨$⟩ x)

  .∘-resp-≡′ : ∀ {A B C} {f h : B ⟶ C} {g i : A ⟶ B} → f ≡′ h → g ≡′ i → f ∘′ g ≡′ h ∘′ i
  ∘-resp-≡′ {C = C} {h = h} f≡h g≡i {x} = Setoid.trans C f≡h (cong h g≡i)

Setoids : ∀ c ℓ → Category (suc (ℓ ⊔ c)) (ℓ ⊔ c)
Setoids c ℓ = QCategory.category (SetoidsQ c ℓ)

-- setoids with irrelevant equality
ISetoidsQ : ∀ c ℓ → QCategory (suc (ℓ ⊔ c)) (ℓ ⊔ c) (ℓ ⊔ c)
ISetoidsQ c ℓ = record
  { Obj = Setoid c ℓ
  ; _⇒_ = _⟶_
  ; _≡_ = λ {A B} → Relation.Binary.Setoid._≈_ (setoid-i→r (A ⇨ B))
  ; compose = _∙_
  ; id = id′
  ; assoc = λ {A B C D} {f g h} →
                squash (cong (h ∙ g ∙ f))
  ; identityˡ = λ {A B f} → squash (cong f)
  ; identityʳ = λ {A B f} → squash (cong f)
  ; equiv = λ {A B} → Relation.Binary.Setoid.isEquivalence (setoid-i→r (A ⇨ B))
  ; ∘-resp-≡ = λ f≡h g≡i → squash (λ x≡y → anonymous-witness f≡h (anonymous-witness g≡i x≡y))
  }
  where
  open Relation.Binary using (Rel)
  open Categories.Support.Equivalence
  open Categories.Support.SetoidFunctions renaming (id to id′)

ISetoids : ∀ c ℓ → Category (suc (ℓ ⊔ c)) (ℓ ⊔ c)
ISetoids c ℓ = QCategory.category (ISetoidsQ c ℓ)