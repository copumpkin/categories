{-# OPTIONS --universe-polymorphism #-}
module Categories.Equivalence.Strong where

-- Strong equivalence of categories.  Same as ordinary equivalence in Cat.
-- May not include everything we'd like to think of as equivalences, namely
-- the full, faithful functors that are essentially surjective on objects.

open import Level
open import Relation.Binary using (IsEquivalence; module IsEquivalence)
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Functor hiding (equiv)
open import Categories.NaturalIsomorphism as NI hiding (equiv)
open import Categories.NaturalTransformation as NT hiding (id; equiv)
open import Categories.Morphisms using (Iso; module Iso)

record WeakInverse {o a o′ a′} {C : Category o a} {D : Category o′ a′} (F : Functor C D) (G : Functor D C) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    F∘G≅id : NaturalIsomorphism (F ∘ G) id
    G∘F≅id : NaturalIsomorphism (G ∘ F) id
  F∘G⇒id = NaturalIsomorphism.F⇒G F∘G≅id
  id⇒F∘G = NaturalIsomorphism.F⇐G F∘G≅id
  G∘F⇒id = NaturalIsomorphism.F⇒G G∘F≅id
  id⇒G∘F = NaturalIsomorphism.F⇐G G∘F≅id
  .F∘G-iso : _
  F∘G-iso = NaturalIsomorphism.iso F∘G≅id
  .F∘G-isoˡ : _
  F∘G-isoˡ = λ x → Iso.isoˡ D (F∘G-iso x)
  .F∘G-isoʳ : _
  F∘G-isoʳ = λ x → Iso.isoʳ D (F∘G-iso x)
  .G∘F-iso : _
  G∘F-iso = NaturalIsomorphism.iso G∘F≅id
  .G∘F-isoˡ : _
  G∘F-isoˡ = λ x → Iso.isoˡ C (G∘F-iso x)
  .G∘F-isoʳ : _
  G∘F-isoʳ = λ x → Iso.isoʳ C (G∘F-iso x)

record StrongEquivalence {o a o′ a′} (C : Category o a) (D : Category o′ a′) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    F : Functor C D
    G : Functor D C
    weak-inverse : WeakInverse F G
  open WeakInverse weak-inverse public

module Equiv where
  refl : ∀ {o a} {C : Category o a} → StrongEquivalence C C
  refl = record
    { F = id
    ; G = id
    ; weak-inverse = record
      { F∘G≅id = IsEquivalence.refl NI.equiv
      ; G∘F≅id = IsEquivalence.refl NI.equiv
      }
    }

  sym : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} → StrongEquivalence C D → StrongEquivalence D C
  sym Inv = record
    { F = Inv.G
    ; G = Inv.F
    ; weak-inverse = record
      { F∘G≅id = Inv.G∘F≅id
      ; G∘F≅id = Inv.F∘G≅id
      }
    }
    where
    module Inv = StrongEquivalence Inv

  trans : ∀ {o₁ a₁ o₂ a₂ o₃ a₃} {C₁ : Category o₁ a₁} {C₂ : Category o₂ a₂} {C₃ : Category o₃ a₃} → StrongEquivalence C₁ C₂ → StrongEquivalence C₂ C₃ → StrongEquivalence C₁ C₃
  trans {C₁ = C₁} {C₂} {C₃} A B = record
    { F = B.F ∘ A.F
    ; G = A.G ∘ B.G
    ; weak-inverse = record
      { F∘G≅id = IsEquivalence.trans NI.equiv ((B.F ⓘˡ A.F∘G≅id) ⓘʳ B.G) B.F∘G≅id
      ; G∘F≅id = IsEquivalence.trans NI.equiv ((A.G ⓘˡ B.G∘F≅id) ⓘʳ A.F) A.G∘F≅id
      }
    }
    where
    module A = StrongEquivalence A
    module B = StrongEquivalence B

equiv : ∀ {o a} → IsEquivalence (StrongEquivalence {o} {a})
equiv = record { refl = Equiv.refl; sym = Equiv.sym; trans = Equiv.trans }