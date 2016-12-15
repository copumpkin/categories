{-# OPTIONS --universe-polymorphism #-}

module Categories.Groupoid.Coproduct where

open import Level
open import Data.Sum

open import Categories.Category
open import Categories.Groupoid
open import Categories.Morphisms
import Categories.Coproduct as CoproductC

Coproduct : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
          → Groupoid C → Groupoid D → Groupoid (CoproductC.Coproduct C D)
Coproduct C D = record
  { _⁻¹ = λ { {inj₁ _} {inj₁ _} → λ { {lift f} → lift (C._⁻¹ f) }
            ; {inj₁ _} {inj₂ _} (lift ())
            ; {inj₂ _} {inj₁ _} (lift ())
            ; {inj₂ _} {inj₂ _} → λ { {lift f} → lift (D._⁻¹ f) }
            }
  ; iso = λ { {inj₁ _} {inj₁ _} → record { isoˡ = lift (Iso.isoˡ C.iso)
                                         ; isoʳ = lift (Iso.isoʳ C.iso) }
            ; {inj₁ _} {inj₂ _} {lift ()}
            ; {inj₂ _} {inj₁ _} {lift ()}
            ; {inj₂ _} {inj₂ _} → record { isoˡ = lift (Iso.isoˡ D.iso)
                                         ; isoʳ = lift (Iso.isoʳ D.iso) }
            }
  }
  where
  module C = Groupoid C
  module D = Groupoid D
