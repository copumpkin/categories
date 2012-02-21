{-# OPTIONS --universe-polymorphism #-}
module Categories.Opposite where

-- some properties of the opposite category.
-- XXX these should probably go somewhere else, but everywhere i think of
-- has other problems. ☹

open import Categories.Category
open import Categories.Morphisms renaming (_≅_ to _[_≅_])

opⁱ : ∀ {o a} {C : Category o a} {A B} → C [ A ≅ B ] → Category.op C [ B ≅ A ]
opⁱ {C = C} A≅B = record
  { f = A≅B.f
  ; g = A≅B.g
  ; iso = record { isoˡ = A≅B.isoʳ; isoʳ = A≅B.isoˡ }
  }
  where
  module A≅B = _≅_ C A≅B
