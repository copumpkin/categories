{-# OPTIONS --universe-polymorphism --irrelevant-projections #-}
module Categories.Support.Equivalence where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; IsPreorder; Preorder; Reflexive; Transitive; Symmetric; _⇒_) renaming (Setoid to RSetoid; module Setoid to RSetoid)
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Pointwise.NonDependent using (×-isEquivalence)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    .isEquivalence : IsEquivalence _≈_

  .refl : Reflexive _≈_
  refl = IsEquivalence.refl isEquivalence
  .trans : Transitive _≈_
  trans = IsEquivalence.trans isEquivalence
  .sym : Symmetric _≈_
  sym = IsEquivalence.sym isEquivalence
  .reflexive : _≡_ ⇒ _≈_
  reflexive = IsEquivalence.reflexive isEquivalence

  .isPreorder : IsPreorder _≡_ _≈_
  isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

  .preorder : Preorder c c ℓ
  preorder = record { isPreorder = isPreorder }

  -- A trivially indexed setoid.

  {-
  indexedSetoid : ∀ {i} {I : Set i} → I.Setoid I c _
  indexedSetoid = record
    { Carrier = λ _ → Carrier
    ; _≈_     = _≈_
    ; isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }
    }
  -}

setoid-r→i : ∀ {c ℓ} → RSetoid c ℓ → Setoid c ℓ
setoid-r→i Base = record
  { Carrier = Base.Carrier
  ; _≈_ = Base._≈_
  ; isEquivalence = Base.isEquivalence
  }
  where module Base = RSetoid Base

record I→R-Wrapper {c ℓ} {Carrier : Set c} (Base : Rel Carrier ℓ) (x y : Carrier) : Set ℓ where
  constructor squash
  field
    .anonymous-witness : Base x y

setoid-i→r : ∀ {c ℓ} → Setoid c ℓ → RSetoid c ℓ
setoid-i→r Base = record
  { Carrier = Base.Carrier
  ; _≈_ = I→R-Wrapper Base._≈_
  ; isEquivalence = record
    { refl = squash Base.refl
    ; sym = λ pf → squash (Base.sym (anonymous-witness pf))
    ; trans = λ i≈j j≈k → squash (Base.trans (anonymous-witness i≈j) (anonymous-witness j≈k))
    }
  }
  where
  module Base = Setoid Base
  open I→R-Wrapper

set→setoid : ∀ {ℓ} → Set ℓ → Setoid ℓ ℓ
set→setoid Base = record
  { Carrier = Base
  ; _≈_ = _≡_
  ; isEquivalence = PropEq.isEquivalence
  }

_×-setoid_ : ∀ {s₁ s₂ s₃ s₄} → Setoid s₁ s₂ → Setoid s₃ s₄ → Setoid _ _
S₁ ×-setoid S₂ = record
  { isEquivalence = ×-isEquivalence (isEquivalence S₁)  (isEquivalence S₂)
  } where open Setoid

Lift-setoid : ∀ {c ℓ a b} -> Setoid c ℓ -> Setoid (c ⊔ a) (ℓ ⊔ b)
Lift-setoid {c} {ℓ} {a} {b} s = record {
    Carrier = Lift {c} a Carrier;
    _≈_ = λ x₁ x₂ → Lift {ℓ} b (lower x₁ ≈ lower x₂);
    isEquivalence = record {
        refl = lift refl;
        sym = λ x₁ → lift (sym (lower x₁));
        trans = λ x₁ x₂ → lift (trans (lower x₁) (lower x₂))}}
 where
   open Setoid s

∀[_]-setoid_ : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → (A → Setoid s₁ s₂) → Setoid _ _
∀[ A ]-setoid B = record
   { Carrier = ∀ a → B.Carrier a
   ; _≈_ = λ f g → ∀ a → B._≈_ a (f a) (g a)
   ; isEquivalence = record
       { refl = λ a → B.refl a
       ; sym = λ f≈g a → B.sym a (f≈g a)
       ; trans = λ f≈g g≈h a → B.trans a (f≈g a) (g≈h a)
       }
   }
  where
    module B a = Setoid (B a)

Fam-setoid : ∀ {ℓ s₁ s₂} → (A : Set ℓ) → (B : Setoid s₁ s₂) → (A → Setoid.Carrier B) → Setoid _ _
Fam-setoid A B p = record
  { Carrier = A
  ; _≈_ = λ a₁ a₂ → p a₁ ≈ p a₂
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  }
 where
   open Setoid B
