{-# OPTIONS --universe-polymorphism #-}
-- in a lot of cases we have a relation that is already reflexive and symmetric
-- and we want to make it symmetric
open import Level
open import Relation.Binary
open import Relation.Binary.On using () renaming (isEquivalence to on-preserves-equivalence)

module Categories.Support.ZigZag {c ℓ₁ ℓ₂} (Base : Preorder c ℓ₁ ℓ₂) where

open import Categories.Support.Equivalence using () renaming (Setoid to ISetoid; module Setoid to ISetoid)
open Preorder Base

data Direction : Set where
  ↘ ↗ : Direction

rotate : Direction → Direction
rotate ↘ = ↗
rotate ↗ = ↘

data ZigZag : (x y : Carrier) (begin end : Direction) → Set (c ⊔ ℓ₂) where
  zig : ∀ {x y z e} (first : x ∼ y) (rest : ZigZag y z ↗ e) → ZigZag x z ↘ e
  zag : ∀ {x y z e} (first : y ∼ x) (rest : ZigZag y z ↘ e) → ZigZag x z ↗ e
  slish : ∀ {x y} (last : x ∼ y) → ZigZag x y ↘ ↘
  slash : ∀ {x y} (last : y ∼ x) → ZigZag x y ↗ ↗

zz-sym′ : ∀ {x y z begin middle end} → ZigZag y z middle end → ZigZag y x middle begin → ZigZag z x (rotate end) begin
zz-sym′ (zig first rest) accum = zz-sym′ rest (zag first accum)
zz-sym′ (zag first rest) accum = zz-sym′ rest (zig first accum)
zz-sym′ (slish last) accum = zag last accum
zz-sym′ (slash last) accum = zig last accum

zz-sym : ∀ {x y begin end} → ZigZag x y begin end → ZigZag y x (rotate end) (rotate begin)
zz-sym (zig first rest) = zz-sym′ rest (slash first)
zz-sym (zag first rest) = zz-sym′ rest (slish first)
zz-sym (slish last) = slash last
zz-sym (slash last) = slish last

zz-trans : ∀ {x y z begin end begin′ end′} → ZigZag x y begin end → ZigZag y z begin′ end′ → ZigZag x z begin end′
zz-trans (zig first rest) yz = zig first (zz-trans rest yz)
zz-trans (zag first rest) yz = zag first (zz-trans rest yz)
zz-trans (slish last) (zig first rest) = zig (trans last first) rest
zz-trans (slish last) (zag first rest) = zig last (zag first rest)
zz-trans (slish last) (slish only) = slish (trans last only)
zz-trans (slish last) (slash only) = zig last (slash only)
zz-trans (slash last) (zig first rest) = zag last (zig first rest)
zz-trans (slash last) (zag first rest) = zag (trans first last) rest
zz-trans (slash last) (slish only) = zag last (slish only)
zz-trans (slash last) (slash only) = slash (trans only last)

data Alternating (x y : Carrier) : Set (c ⊔ ℓ₂) where
  disorient : ∀ {begin end} (zz : ZigZag x y begin end) → Alternating x y

is-equivalence : IsEquivalence Alternating
is-equivalence = record
  { refl = disorient (slash refl)
  ; sym = my-sym
  ; trans = my-trans
  }
  where
  module Base = Preorder Base
  my-sym : ∀ {i j} → Alternating i j → Alternating j i
  my-sym (disorient zz) = disorient (zz-sym zz)
  my-trans : ∀ {i j k} → Alternating i j → Alternating j k → Alternating i k
  my-trans (disorient ij) (disorient jk) = disorient (zz-trans ij jk)

setoid : Setoid c (c ⊔ ℓ₂)
setoid = record
  { Carrier = Carrier
  ; _≈_ = Alternating
  ; isEquivalence = is-equivalence }

isetoid : ISetoid c (c ⊔ ℓ₂)
isetoid = record
  { Carrier = Carrier
  ; _≈_ = Alternating
  ; isEquivalence = is-equivalence }

-- the main eliminators for Alternating -- they prove that any equivalence that
-- respects the base preorder also respects its Alternating completion.

locally-minimal : ∀ {ℓ′} {_≈_ : Rel Carrier ℓ′} (≈-isEquivalence : IsEquivalence _≈_) → (_∼_ ⇒ _≈_) → (Alternating ⇒ _≈_)
locally-minimal {_≈_ = _≋_} isEq inj (disorient zz) = impl zz
  where
  open IsEquivalence isEq renaming (trans to _>trans>_)

  impl : ∀ {i j b e} → ZigZag i j b e → i ≋ j
  impl (zig first rest) = inj first >trans> impl rest
  impl (zag first rest) = sym (inj first) >trans> impl rest
  impl (slish last) = inj last
  impl (slash last) = sym (inj last)

minimal : ∀ {c′ ℓ′} (Dest : Setoid c′ ℓ′) (f : Carrier → Setoid.Carrier Dest) → (_∼_ =[ f ]⇒ Setoid._≈_ Dest) → (Alternating =[ f ]⇒ Setoid._≈_ Dest)
minimal Dest f inj = locally-minimal (on-preserves-equivalence f (Setoid.isEquivalence Dest)) inj

.iminimal : ∀ {c′ ℓ′} (Dest : ISetoid c′ ℓ′) (f : Carrier → ISetoid.Carrier Dest) → (_∼_ =[ f ]⇒ ISetoid._≈_ Dest) → (Alternating =[ f ]⇒ ISetoid._≈_ Dest)
iminimal Dest f inj = locally-minimal (on-preserves-equivalence f (ISetoid.isEquivalence Dest)) inj