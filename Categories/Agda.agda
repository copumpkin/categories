{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda where

open import Level
import Relation.Binary
import Relation.Binary.HeterogeneousEquality as H
import Function.Equality

import Categories.Support.Equivalence
import Categories.Support.SetoidFunctions

open import Categories.Support.PropositionalEquality
open import Categories.Support.Quotients
open import Categories.Category
open import Categories.Category.Quotient
open import Categories.Functor using (Functor)

Setsᵉ : ∀ o → EasyCategory _ _ _
Setsᵉ o = record
  { Obj = Set o
  ; _⇒_ = λ d c → d → c
  ; _≡_ = λ f g → ∀ {x} → f x ≣ g x

  ; _∘_ = λ f g x → f (g x)
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
  ; _∘_ = _∙_
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


Lift-IS : ∀ {c ℓ} a b → Functor (ISetoids c ℓ) (ISetoids (c ⊔ a) (ℓ ⊔ b))
Lift-IS {c} {ℓ} a b = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = qelim-compute′ F₁-cong
  ; homomorphism = λ {X Y Z f g} → let open Out.HomReasoning in
      qequate′ {ℓ ⊔ c} {ℓ ⊔ c} {b ⊔ (a ⊔ (ℓ ⊔ c))} {X ⟶ Y} {InQ._≡_} {InQ.equiv} {my-F₀ X Out.⇒ my-F₀ Z} {λ f′ → my-F₁ (g In.∘ f′)} {λ f′ → my-F₁ g Out.∘ my-F₁ f′} (λ f′ → qequate′ {ℓ ⊔ c} {ℓ ⊔ c} {b ⊔ (a ⊔ (ℓ ⊔ c))} {Y ⟶ Z} {InQ._≡_} {InQ.equiv} {my-F₀ X Out.⇒ my-F₀ Z} {λ g′ → my-F₁ (g′ In.∘ ⌊ f′ ⌉)} {λ g′ → my-F₁ g′ Out.∘ my-F₁ ⌊ f′ ⌉} (λ g′ →
      begin
        my-F₁ (⌊ g′ ⌉ In.∘ ⌊ f′ ⌉)
      ↓⟨ ≣-cong my-F₁ InQ.⊘-compute₂ ⟩
        my-F₁ ⌊ g′ InQ.∘ f′ ⌉
      ↓⟨ qelim-compute′ F₁-cong ⟩
        F₁-app (g′ InQ.∘ f′)
      ↑⟨ OutQ.⊘-compute₂ ⟩
        F₁-app g′ Out.∘ F₁-app f′
      ↑⟨ qelim-compute′ F₁-cong ⟩∘⟨ qelim-compute′ F₁-cong ⟩
        my-F₁ ⌊ g′ ⌉ Out.∘ my-F₁ ⌊ f′ ⌉
      ∎) g) f
      -- λ {_} {_} {_} {f} {g} eq → lift (cong g (cong f (lower eq)))

  }
  where
  open import Categories.Support.Equivalence
  open Categories.Support.SetoidFunctions renaming (id to id′)
  module In   =  Category (ISetoids   c       ℓ)
  module InQ  = QCategory (ISetoidsQ  c       ℓ) 
  module Out  =  Category (ISetoids  (a ⊔ c) (b ⊔ ℓ))
  module OutQ = QCategory (ISetoidsQ (a ⊔ c) (b ⊔ ℓ))

  my-F₀ : Setoid c ℓ → Setoid (c ⊔ a) (ℓ ⊔ b)
  my-F₀ = Lift-setoid {c} {ℓ} {a} {b}

  F₁-app : ∀ {A B} → (A InQ.⇒ B) → my-F₀ A Out.⇒ my-F₀ B
  F₁-app f = ⌊ record { _⟨$⟩_ = λ x → lift (f ⟨$⟩ (lower x)); cong = λ eq → lift (cong f (lower eq)) } ⌉

  F₁-cong : ∀ {A B} {f g : A InQ.⇒ B} → f InQ.≡ g → F₁-app f ≣ F₁-app g
  F₁-cong eq = qdiv (squash (λ {x y} eq′ → lift (anonymous-witness eq (lower eq′))))

  my-F₁ : ∀ {A B : In.Obj} → (A In.⇒ B) → (my-F₀ A Out.⇒ my-F₀ B)
  my-F₁ = qelim′ F₁-app F₁-cong

Lift-Sets : ∀ {ℓ} a → Functor (Sets ℓ) (Sets (ℓ ⊔ a))
Lift-Sets {ℓ} a = record
  { F₀ = Lift {ℓ} {a}
  ; F₁ = λ f x → lift (f (lower x))
  ; identity = ≣-ext (λ { (lift x) → ≣-refl })
  ; homomorphism = λ {_} {_} {_} {f} {g} → ≣-refl
  }
