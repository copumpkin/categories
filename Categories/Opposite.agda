{-# OPTIONS --universe-polymorphism #-}
module Categories.Opposite where

-- some properties of the opposite category.
-- XXX these should probably go somewhere else, but everywhere i think of
-- has other problems. ☹

open import Categories.Category
open import Categories.Functor
open import Categories.FunctorCategory
open import Categories.NaturalTransformation
open import Categories.Morphisms renaming (_≅_ to _[_≅_])

opⁱ : ∀ {o ℓ e} {C : Category o ℓ e} {A B} → C [ A ≅ B ] → Category.op C [ B ≅ A ]
opⁱ {C = C} A≅B = record
  { f = A≅B.f
  ; g = A≅B.g
  ; iso = record { isoˡ = A≅B.isoʳ; isoʳ = A≅B.isoˡ }
  }
  where
  module A≅B = Categories.Morphisms._≅_ A≅B

opF : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} -> 
    (Functor (Category.op (Functors (Category.op A) (Category.op B))) (Functors A B))
opF {A = A} {B} = record {
                    F₀ = Functor.op;
                    F₁ = NaturalTransformation.op;
                    identity = Category.Equiv.refl B;
                    homomorphism = Category.Equiv.refl B;
                    F-resp-≡ = λ x → x }
