{-# OPTIONS --universe-polymorphism #-}
-- in a lot of cases we have a relation that is already reflexive and symmetric
-- and we want to make it symmetric
module Categories.Support.ZigZag where

open import Level
open import Relation.Binary
open import Relation.Binary.Construct.On using () renaming (isEquivalence to on-preserves-equivalence)

open import Categories.Support.Equivalence using () renaming (Setoid to ISetoid; module Setoid to ISetoid)

data Direction : Set where
  ↘ ↗ : Direction

rotate : Direction → Direction
rotate ↘ = ↗
rotate ↗ = ↘


data ZigZag′ {c ℓ₂} {Carrier : Set c} (_∼_ : Carrier -> Carrier -> Set ℓ₂) : (x y : Carrier) (begin end : Direction) → Set (c ⊔ ℓ₂) where
  zig : ∀ {x y z e} (first : x ∼ y) (rest : ZigZag′ _∼_ y z ↗ e) → ZigZag′ _∼_ x z ↘ e
  zag : ∀ {x y z e} (first : y ∼ x) (rest : ZigZag′ _∼_ y z ↘ e) → ZigZag′ _∼_ x z ↗ e
  slish : ∀ {x y} (last : x ∼ y) → ZigZag′ _∼_ x y ↘ ↘
  slash : ∀ {x y} (last : y ∼ x) → ZigZag′ _∼_ x y ↗ ↗

ZigZag : ∀ {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) → (x y : Preorder.Carrier Base) (begin end : Direction) → Set (c ⊔ ℓ₂)
ZigZag Base = ZigZag′ (Preorder._∼_ Base)

zz-sym′ : ∀ {c ℓ₁ ℓ₂} {Base : Preorder c ℓ₁ ℓ₂} {x y z begin middle end} → ZigZag Base y z middle end → ZigZag Base y x middle begin → ZigZag Base z x (rotate end) begin
zz-sym′ {Base = Base} (zig first rest) accum = zz-sym′ {Base = Base} rest (zag first accum)
zz-sym′ {Base = Base} (zag first rest) accum = zz-sym′ {Base = Base} rest (zig first accum)
zz-sym′ (slish last) accum = zag last accum
zz-sym′ (slash last) accum = zig last accum

zz-sym : ∀ {c ℓ₁ ℓ₂} {Base : Preorder c ℓ₁ ℓ₂} {x y begin end} → ZigZag Base x y begin end → ZigZag Base y x (rotate end) (rotate begin)
zz-sym {Base = Base} (zig first rest) = zz-sym′ {Base = Base} rest (slash first)
zz-sym {Base = Base} (zag first rest) = zz-sym′ {Base = Base} rest (slish first)
zz-sym (slish last) = slash last
zz-sym (slash last) = slish last

zz-trans : ∀ {c ℓ₁ ℓ₂} {Base : Preorder c ℓ₁ ℓ₂} {x y z begin end begin′ end′} → ZigZag Base x y begin end → ZigZag Base y z begin′ end′ → ZigZag Base x z begin end′
zz-trans {Base = Base} (zig first rest) yz = zig first (zz-trans {Base = Base} rest yz)
zz-trans {Base = Base} (zag first rest) yz = zag first (zz-trans {Base = Base} rest yz)
zz-trans {Base = Base} (slish last) (zig first rest) = zig (Preorder.trans Base last first) rest
zz-trans (slish last) (zag first rest) = zig last (zag first rest)
zz-trans {Base = Base} (slish last) (slish only) = slish (Preorder.trans Base last only)
zz-trans (slish last) (slash only) = zig last (slash only)
zz-trans (slash last) (zig first rest) = zag last (zig first rest)
zz-trans {Base = Base} (slash last) (zag first rest) = zag (Preorder.trans Base first last) rest
zz-trans (slash last) (slish only) = zag last (slish only)
zz-trans {Base = Base} (slash last) (slash only) = slash (Preorder.trans Base only last)

data Alternating′ {c ℓ₂} {Carrier : Set c} (_∼_ : Carrier -> Carrier -> Set ℓ₂) (x y : Carrier) : Set (c ⊔ ℓ₂) where
  disorient : ∀ {begin end} (zz : ZigZag′ _∼_ x y begin end) → Alternating′ _∼_ x y

Alternating : ∀ {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) → (x y : Preorder.Carrier Base) → Set (c ⊔ ℓ₂)
Alternating Base = Alternating′ (Preorder._∼_ Base)

is-equivalence : ∀ {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) → IsEquivalence (Alternating Base)
is-equivalence Base = record
  { refl = disorient (slash (Base.refl))
  ; sym = my-sym
  ; trans = my-trans
  }
  where
  module Base = Preorder Base
  my-sym : ∀ {i j} → Alternating Base i j → Alternating Base j i
  my-sym (disorient zz) = disorient (zz-sym {Base = Base} zz)
  my-trans : ∀ {i j k} → Alternating Base i j → Alternating Base j k → Alternating Base i k
  my-trans (disorient ij) (disorient jk) = disorient (zz-trans {Base = Base} ij jk)

setoid : ∀ {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) → Setoid c (c ⊔ ℓ₂)
setoid Base = record
  { Carrier = Preorder.Carrier Base
  ; _≈_ = Alternating Base
  ; isEquivalence = is-equivalence Base }

isetoid : ∀ {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) → ISetoid c (c ⊔ ℓ₂)
isetoid Base = record
  { Carrier = Preorder.Carrier Base
  ; _≈_ = Alternating Base
  ; isEquivalence = is-equivalence Base }

-- the main eliminators for Alternating -- they prove that any equivalence that
-- respects the base preorder also respects its Alternating completion.

locally-minimal : ∀ {c ℓ₁ ℓ₂ ℓ′} (Base : Preorder c ℓ₁ ℓ₂) {_≈_ : Rel (Preorder.Carrier Base) ℓ′} (≈-isEquivalence : IsEquivalence _≈_) → (Preorder._∼_ Base ⇒ _≈_) → (Alternating Base ⇒ _≈_)
locally-minimal Base {_≋_} isEq inj (disorient zz) = impl zz
  where
  open IsEquivalence isEq renaming (trans to _>trans>_)

  impl : ∀ {i j b e} → ZigZag Base i j b e → i ≋ j
  impl (zig first rest) = inj first >trans> impl rest
  impl (zag first rest) = sym (inj first) >trans> impl rest
  impl (slish last) = inj last
  impl (slash last) = sym (inj last)

minimal : ∀ {c ℓ₁ ℓ₂ c′ ℓ′} (Base : Preorder c ℓ₁ ℓ₂) (Dest : Setoid c′ ℓ′) (f : Preorder.Carrier Base → Setoid.Carrier Dest) → (Preorder._∼_ Base =[ f ]⇒ Setoid._≈_ Dest) → (Alternating Base =[ f ]⇒ Setoid._≈_ Dest)
minimal Base Dest f inj = locally-minimal Base (on-preserves-equivalence f (Setoid.isEquivalence Dest)) inj

.iminimal : ∀ {c ℓ₁ ℓ₂ c′ ℓ′} (Base : Preorder c ℓ₁ ℓ₂) (Dest : ISetoid c′ ℓ′) (f : Preorder.Carrier Base → ISetoid.Carrier Dest) → (Preorder._∼_ Base =[ f ]⇒ ISetoid._≈_ Dest) → (Alternating Base =[ f ]⇒ ISetoid._≈_ Dest)
iminimal Base Dest f inj = locally-minimal Base (on-preserves-equivalence f (ISetoid.isEquivalence Dest)) inj
