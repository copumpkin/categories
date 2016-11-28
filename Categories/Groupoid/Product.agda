{-# OPTIONS --universe-polymorphism #-}

module Categories.Groupoid.Product where

open import Data.Product

open import Categories.Category
open import Categories.Groupoid
open import Categories.Morphisms
import Categories.Product as ProductC

Product : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {C : Category o₁ ℓ₁ e₁} {D : Category o₂ ℓ₂ e₂}
        → Groupoid C → Groupoid D → Groupoid (ProductC.Product C D)
Product c₁ c₂ = record
         { _⁻¹ = λ {(x₁ , x₂) → Groupoid._⁻¹ c₁ x₁
                              , Groupoid._⁻¹ c₂ x₂}
         ; iso = record { isoˡ = Iso.isoˡ (Groupoid.iso c₁)
                               , Iso.isoˡ (Groupoid.iso c₂)
                        ; isoʳ = Iso.isoʳ (Groupoid.iso c₁)
                               , Iso.isoʳ (Groupoid.iso c₂) } }
