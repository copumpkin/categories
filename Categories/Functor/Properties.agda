{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Properties where

open import Relation.Binary using (_Preserves_⟶_)

open import Categories.Category
open import Categories.Functor
import Categories.Morphisms as Morphisms

module FunctorsAlways {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D) where
  open Functor F

  resp-≅ : F₀ Preserves Morphisms._≅_ C ⟶ Morphisms._≅_ D
  resp-≅ I = record
    { f = F₁ I.f
    ; g = F₁ I.g
    ; iso = record
      { isoˡ = begin
                 D [ F₁ I.g ∘ F₁ I.f ]
               ↑⟨ homomorphism ⟩
                 F₁ (C [ I.g ∘ I.f ])
               ↓⟨ F-resp-≡ (isoˡ I.iso) ⟩
                 F₁ (Category.id C)
               ↓⟨ identity ⟩
                 Category.id D
               ∎
      ; isoʳ = begin
                 D [ F₁ I.f ∘ F₁ I.g ]
               ↑⟨ homomorphism ⟩
                 F₁ (C [ I.f ∘ I.g ])
               ↓⟨ F-resp-≡ (isoʳ I.iso) ⟩
                 F₁ (Category.id C)
               ↓⟨ identity ⟩
                 Category.id D
               ∎
      }
    }
    where
    module I = Morphisms._≅_ C I
    open Morphisms.Iso C
    open Category.HomReasoning D
