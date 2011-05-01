{-# OPTIONS --universe-polymorphism #-}
module Category.Agda where

open import Support
open import Category

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

Setoids : ∀ c ℓ → Category (suc (ℓ ⊔ c)) (ℓ ⊔ c) (ℓ ⊔ c)
Setoids c ℓ = record
  { Obj = Setoid c ℓ
  ; _⇒_ = Hom′
  ; _≡_ = λ {X} {Y} → _≡′_ {X} {Y}
  ; _∘_ = λ {A} {B} {C} → _∘′_ {A} {B} {C}
  ; id = record { F = λ x → x ; cong = λ pf → pf }
  ; assoc = λ {_} {_} {_} {D} → IsEquivalence.refl (Setoid.isEquivalence D)
  ; identityˡ = λ {_} {B} → IsEquivalence.refl (Setoid.isEquivalence B)
  ; identityʳ = λ {_} {B} → IsEquivalence.refl (Setoid.isEquivalence B)
  ; equiv = λ {A} {B} → record 
    { refl = IsEquivalence.refl (Setoid.isEquivalence B)
    ; sym = λ f → IsEquivalence.sym (Setoid.isEquivalence B) f
    ; trans = λ f g → IsEquivalence.trans (Setoid.isEquivalence B) f g
    }
  ; ∘-resp-≡ = λ {A} {B} {C} {f} {h} {g} {i} → ∘-resp-≡′ {A} {B} {C} {f} {h} {g} {i}
  }
  where
  infixr 9 _∘′_
  infix  4 _≡′_

  Obj′ = Setoid c ℓ

  Hom′ : Rel Obj′ _
  Hom′ X Y = SetoidFunction X Y

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  _≡′_ {X} {Y} f g = ∀ {x} → Setoid._≈_ Y (SetoidFunction.F f x) (SetoidFunction.F g x)

  _∘′_ : ∀ {A B C} → Hom′ B C → Hom′ A B → Hom′ A C
  f ∘′ g = record { F = λ x → SetoidFunction.F f (SetoidFunction.F g x); cong = λ x → SetoidFunction.cong f (SetoidFunction.cong g x) }

  .∘-resp-≡′ : ∀ {A B C} {f h : Hom′ B C} {g i : Hom′ A B} → f ≡′ h → g ≡′ i → f ∘′ g ≡′ h ∘′ i
  ∘-resp-≡′ {C = C} {h = h} f≡h g≡i {x} = IsEquivalence.trans (Setoid.isEquivalence C) f≡h (SetoidFunction.cong h g≡i)