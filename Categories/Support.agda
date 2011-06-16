{-# OPTIONS --universe-polymorphism #-}

-- Support stuff mostly stolen or adapted from the Agda standard library

module Support where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

-- Maximum.

infixl 6 _⊔_
infixr 2 _×_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

infix 4 _≣_

data _≣_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  ≣-refl : x ≣ x

{-# BUILTIN EQUALITY _≣_ #-}
{-# BUILTIN REFL ≣-refl #-}

≣-trans : ∀ {a} {A : Set a} → ∀ {x y z : A} → y ≣ z → x ≣ y → x ≣ z
≣-trans ≣-refl ≣-refl = ≣-refl

≣-sym : ∀ {a} {A : Set a} → ∀ {x y : A} → x ≣ y → y ≣ x
≣-sym ≣-refl = ≣-refl

≣-subst : ∀ {a p} {A : Set a} → (P : A → Set p) → ∀ {x y} → x ≣ y → P x → P y
≣-subst P ≣-refl x = x

≣-subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
           {x₁ x₂ y₁ y₂} → x₁ ≣ x₂ → y₁ ≣ y₂ → P x₁ y₁ → P x₂ y₂
≣-subst₂ P ≣-refl ≣-refl p = p


≣-cong : ∀ {a b} {A : Set a} {B : Set b}
         (f : A → B) {x y} → x ≣ y → f x ≣ f y
≣-cong f ≣-refl = ≣-refl

≣-cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) {x y u v} → x ≣ y → u ≣ v → f x u ≣ f y v
≣-cong₂ f ≣-refl ≣-refl = ≣-refl

infixr 4 _,_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b


record Σ′ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁′ : A
    .proj₂′ : B proj₁′

open Σ′ public

∃′ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃′ = Σ′ _

∃₂′ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂′ C = ∃ λ a → ∃′ λ b → C a b

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

⟨_,_⟩ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} → (A → B) → (C → D) → A × C → B × D
⟨ f , g ⟩ (x , y) = f x , g y

⟨_&_⟩ : ∀ {a b d} {A : Set a} {B : Set b} {D : Set d} → (A → B) → (A → D) → A → B × D
⟨ f & g ⟩ x = f x , g x

_∙_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∙ g = λ x → f (g x)

∙-assoc : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} {D : {x : A} {y : B x} → C y → Set d} → (f : ∀ {x} {y : B x} (z : C y) → D z) → (g : ∀ {x} (y : B x) → C y) → (h : (x : A) → B x) → {x : A} → (f ∙ (g ∙ h)) x ≣ ((f ∙ g) ∙ h) x
∙-assoc f g h {x} = ≣-refl

_∙′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → C) → (A → B) → (A → C)
f ∙′ g = _∙_ f g

_∙₂_ : ∀ {a b c d}
         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c}
         {D : {x : A} {y : B x} → C y → Set d} →
      (∀ {x} {y : B x} (z : C y) → D z) → (g : (x : A) (y : B x) → C y) →
      ((x : A) (y : B x) → D (g x y))
f ∙₂ g = λ x y → f (g x y)

_∙₃_ : ∀ {a b c d e}
         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c}
         {D : {x : A} {y : B x} → C y → Set d}
         {E : {x : A} {y : B x} {z : C y} → D z → Set e} →
      (∀ {x} {y : B x} {z : C y} (w : D z) → E w) →
      (g : (x : A) (y : B x) (z : C y) → D z) →
      ((x : A) (y : B x) (z : C y) → E (g x y z))
f ∙₃ g = λ x y z → f (g x y z)

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

_$↑_ : ∀ {a b c}
         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
       (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
       ((x : A) → C (g x))
_$↑_ = _∙_

_$⇈_ : ∀ {ℓ a b}
          {T : Set ℓ} {A : T → Set a} {B : (i : T) → (x : A i) → Set b} →
       (f : (i : T) → ∀ (x : A i) → B i x) → (x : (i : T) → A i) →
       ((i : T) → B i (x i))
f $⇈ x = λ i → f i (x i)

{- John Major equality would be nice for stating this result ... -}
$⇈-obs : ∀ {ℓ a b}
           {T : Set ℓ} {A : T → Set a} {B : (i : T) → (x : A i) → Set b} →
         {f f′ : (i : T) → ∀ (x : A i) → B i x}
           (eq-f : ∀ {i} {x : A i} → f i x ≣ f′ i x) →
         {x x′ : (i : T) → A i} (eq-x : ∀ {i} → x i ≣ x′ i) →
         ∀ {i} → (≣-subst (B i) (eq-x {i}) ((f $⇈ x) i) ≣ (f′ $⇈ x′) i)
$⇈-obs eq-f {x} {x′} eq-x {i} rewrite eq-x {i} | eq-f {i} {x′ i} = ≣-refl

lift↑ : ∀ {ℓ a b}
          {T : Set ℓ} {A : T → Set a} {B : (i : T) → A i → Set b} →
        (f : ∀ {i} (x : A i) → B i x) → (x : (i : T) → A i) →
        ((i : T) → B i (x i))
lift↑ = _$↑_

lift↑₂ : ∀ {ℓ a b c}
           {T : Set ℓ} {A : T → Set a} {B : (i : T) → Set b}
           {C : (i : T) → A i → B i → Set c} →
         (f : ∀ {i} (x : A i) (y : B i) → C i x y) →
         (x : (i : T) → A i) (y : (i : T) → B i) →
         ((i : T) → C i (x i) (y i))
lift↑₂ = λ f x y → (lift↑ f x) $⇈ y

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ

private
  _⇒_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
       Rel A ℓ₁ → Rel A ℓ₂ → Set _
  P ⇒ Q = ∀ {i j} → P i j → Q i j

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respects₂ _∼_ =
  (∀ {x} → P x      Respects _∼_) ×
  (∀ {y} → flip P y Respects _∼_)

record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  -- a helper to promote propositional equality to equivalence
  .prop : ∀ {x y} → x ≣ y → x ≈ y
  prop ≣-refl = refl

record IsPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : _≈_ ⇒ _∼_
    trans         : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  module Eq = IsEquivalence isEquivalence

  refl : ∀ {x} → x ∼ x
  refl = reflexive Eq.refl

  ∼-resp-≈ : _∼_ Respects₂ _≈_
  ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive x≈y))
           , (λ x≈y x∼z → trans (reflexive (Eq.sym x≈y)) x∼z)

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public


record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    .isEquivalence : IsEquivalence _≈_

record SetoidFunction {c ℓ c′ ℓ′} (X : Setoid c ℓ) (Y : Setoid c′ ℓ′) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  field
    F : Setoid.Carrier X → Setoid.Carrier Y
    .cong : ∀ {x y} → Setoid._≈_ X x y → Setoid._≈_ Y (F x) (F y)

module SetoidReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open Setoid S

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≈⟨_⟩_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infixr 2 _↓≣⟨_⟩_
  infixr 2 _↑≣⟨_⟩_
  infixr 2 _↕_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : Carrier) : Set s₂ where
    relTo : (x∼y : x ≈ y) → x IsRelatedTo y

  .begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
  begin relTo x∼y = x∼y

  ._↓⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
    where open IsEquivalence isEquivalence

  ._↑⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑⟨ y∼x ⟩ relTo y∼z = relTo (trans (sym y∼x) y∼z)
    where open IsEquivalence isEquivalence

  -- the syntax of the ancients, for compatibility
  ._≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _≈⟨_⟩_ = _↓⟨_⟩_

  ._↓≣⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↑≣⟨_⟩_ : ∀ x {y z} → y ≣ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↕_ : ∀ x {z} → x IsRelatedTo z → x IsRelatedTo z
  _ ↕ x∼z = x∼z

  ._∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl
    where open IsEquivalence isEquivalence

≣-is-equivalence : ∀ {ℓ} (A : Set ℓ) → IsEquivalence (_≣_ {A = A})
≣-is-equivalence A = record { refl = λ {x} → ≣-refl
                            ; sym = λ {x} {y} → ≣-sym
                            ; trans = λ {x} {y} {z} → flip ≣-trans }

SetAsSetoid : ∀ {ℓ} (A : Set ℓ) → Setoid ℓ ℓ
SetAsSetoid A = record { Carrier = A
                       ; _≈_ = _≣_
                       ; isEquivalence = ≣-is-equivalence A }

module ≣-reasoning {ℓ} (S : Set ℓ) where
  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≈⟨_⟩_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infixr 2 _↕_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : S) : Set ℓ where
    relTo : (x∼y : x ≣ y) → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ≣ y
  begin relTo x∼y = x∼y

  -- the syntax of the ancients, for compatibility
  _≈⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x∼y ⟩ relTo y∼z = relTo (≣-trans y∼z x∼y)

  _↓⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓⟨ x∼y ⟩ relTo y∼z = relTo (≣-trans y∼z x∼y)

  _↑⟨_⟩_ : ∀ x {y z} → y ≣ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑⟨ y∼x ⟩ relTo y∼z = relTo (≣-trans y∼z (≣-sym y∼x))

  _↕_ : ∀ x {z} → x IsRelatedTo z → x IsRelatedTo z
  _ ↕ x∼z = x∼z

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo ≣-refl


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

data ⊥ : Set where

¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

record ⊤ {ℓ} : Set ℓ where
  constructor tt

type-signature : ∀ {a} (A : Set a) → A → A
type-signature A x = x

syntax type-signature A x = x ∶ A

data Either {l r : Level} (L : Set l) (R : Set r) : Set (l ⊔ r) where
  inl : L → Either L R
  inr : R → Either L R

either₀ : ∀ {l r ℓ : Level} {L : Set l} {R : Set r} {A : Set ℓ} (f : L → A) (g : R → A) (v : Either L R) → A
either₀ f _ (inl x) = f x
either₀ _ g (inr y) = g y

∙-dist-either₀ : ∀ {l r ℓ ℓ′} {L : Set l} {R : Set r} {A : Set ℓ} {A′ : Set ℓ′} (f : L → A) (g : R → A) (h : A → A′) {v : Either L R} → (h ∙ either₀ f g) v ≣ either₀ (h ∙ f) (h ∙ g) v
∙-dist-either₀ f g h {inl y} = ≣-refl
∙-dist-either₀ f g h {inr y} = ≣-refl

either₀-obsˡ : ∀ {l r ℓ : Level} {L : Set l} {R : Set r} {A : Set ℓ}
                 {f : L → A} {f′ : L → A}
               (eq : ∀ {x} → f x ≣ f′ x) (g : R → A) →
               ∀ {v} → (either₀ f g v ≣ either₀ f′ g v)
either₀-obsˡ eq g {inl y} = eq
either₀-obsˡ eq g {inr y} = ≣-refl

either₀-obsʳ : ∀ {l r ℓ : Level} {L : Set l} {R : Set r} {A : Set ℓ}
                 {g : R → A} {g′ : R → A}
               (f : L → A) (eq : ∀ {x} → g x ≣ g′ x) →
               ∀ {v} → (either₀ f g v ≣ either₀ f g′ v)
either₀-obsʳ f eq {inl y} = ≣-refl
either₀-obsʳ f eq {inr y} = eq

either₀-correlate : ∀ {l r ℓ ℓ′ : Level} {L : Set l} {R : Set r} {A : Set ℓ} {A′ : Set ℓ′ } (f : L → A′ → A) (g : R → A′ → A) (f′ : L → A′) (g′ : R → A′) (v : Either L R) → either₀ (either₀ f g v ∙ f′) (either₀ f g v ∙ g′) v ≣ either₀ (f $⇈ f′) (g $⇈ g′) v
either₀-correlate f g f′ g′ (inl v) = ≣-refl
either₀-correlate f g f′ g′ (inr v) = ≣-refl

either : ∀ {l r ℓ} {L : Set l} {R : Set r} {L′ : L → Set ℓ} {R′ : R → Set ℓ} (f : (x : L) → L′ x) (g : (y : R) → R′ y) (v : Either L R) → either₀ L′ R′ v
either f _ (inl x) = f x
either _ g (inr y) = g y

either′ : ∀ {l r ℓ} {L : Set l} {R : Set r} {A : Either L R → Set ℓ} (f : (x : L) → A (inl x)) (g : (y : R) → A (inr y)) (v : Either L R) → A v
either′ f _ (inl x) = f x
either′ _ g (inr y) = g y

left : ∀ {l l′ r} {L : Set l} {R : Set r} {L′ : Set l′} (f : L → L′) (v : Either L R) → Either L′ R
left f (inl x) = inl (f x)
left _ (inr y) = inr y

right : ∀ {l r r′} {L : Set l} {R : Set r} {R′ : Set r′} (g : R → R′) (v : Either L R) → Either L R′
right _ (inl x) = inl x
right g (inr y) = inr (g y)

_+++_ : ∀ {l l′} {L : Set l} {L′ : Set l′} (f : L → L′) {r r′} {R : Set r} {R′ : Set r′} (g : R → R′) (v : Either L R) → Either L′ R′
(f +++ _) (inl x) = inl (f x)
(_ +++ g) (inr y) = inr (g y) 

uncurry₀ : ∀ {x y z} {X : Set x} {Y : Set y} {Z : Set z} (f : X → Y → Z) → X × Y → Z
uncurry₀ f (x , y) = f x y

∙-commute-uncurry₀ : ∀ {x y z z′} {X : Set x} {Y : Set y} {Z : Set z} {Z′ : Set z′} (g : Z → Z′) (f : X → Y → Z) → (g ∙ uncurry₀ f) ≣ uncurry₀ (g ∙₂ f)
∙-commute-uncurry₀ g f = ≣-refl

∙₂-commute-uncurry₀ : ∀ {x y z w w′} {X : Set x} {Y : Set y} {Z : Set z} {W : Set w} {W′ : Set w′} (g : W → W′) (f : X → Y → Z → W) → (g ∙₂ uncurry₀ f) ≣ uncurry₀ (g ∙₃ f)
∙₂-commute-uncurry₀ g f = ≣-refl

uncurry₀-obs : ∀ {x y z} {X : Set x} {Y : Set y} {Z : Set z} {f : X → Y → Z} → (f-obs : ∀ {x x′ y y′} → x ≣ x′ → y ≣ y′ → f x y ≣ f x′ y′) {x,y x,y′ : X × Y} (eq : x,y ≣ x,y′) → uncurry₀ f x,y ≣ uncurry₀ f x,y′
uncurry₀-obs f-obs eq rewrite f-obs (≣-cong fst eq) (≣-cong snd eq) = ≣-refl

uncurry₀-obs′₁ : ∀ {x y z w} {X : Set x} {Y : Set y} {Z : Set z} {W : Z → Set w} {f f′ : X → Y → (c : Z) → W c} → (∀ a b c → f a b c ≣ f′ a b c) → ∀ a,b c → uncurry₀ f a,b c ≣ uncurry₀ f′ a,b c
uncurry₀-obs′₁ f-obs a,b c rewrite f-obs (fst a,b) (snd a,b) c = ≣-refl

uncurry : ∀ {x y z} {X : Set x} {Y : Set y} {Z : X → Y → Set z} (f : (x : X) → (y : Y) → Z x y) → (x,y : X × Y) → uncurry₀ Z x,y
uncurry f (x , y) = f x y

prop→obs : ∀ {a b} {A : Set a} {B : A → Set b} {f : (x : A) → B x} {g : (x : A) → B x} (eq : f ≣ g) → ∀ {x} → f x ≣ g x
prop→obs ≣-refl {x} = ≣-refl
