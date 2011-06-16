{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.Equivalence where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; IsPreorder; Preorder; Reflexive; Transitive; Symmetric; _⇒_)
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
