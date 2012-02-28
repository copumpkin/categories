open import Categories.Category

module Categories.FunctorCategory.Morphisms {o a o′ a′} (C : Category o a) (D : Category o′ a′) where

open import Categories.FunctorCategory
import Categories.Morphisms as Mor
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation renaming (promote to promoteNT; id to idⁿ)

open Category (Functors C D)
open Mor (Functors C D)

NI→Iso : ∀ F G → NaturalIsomorphism F G → F ≅ G
NI→Iso F G ni = record
  { f = F⇒G
  ; g = F⇐G
  ; iso = record { isoˡ = promoteNT (F⇐G ∘ F⇒G) id (dl (iso _))
                 ; isoʳ = promoteNT (F⇒G ∘ F⇐G) id (dr (iso _)) }
  }
  where
  open NaturalIsomorphism ni
  open Mor.Iso D renaming (isoˡ to dl; isoʳ to dr)
