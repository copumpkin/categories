{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Properties where

open import Relation.Binary using (_Preserves_⟶_)

open import Categories.Category
open import Categories.Functor
import Categories.Morphisms as Morphisms

module FunctorsAlways {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D) where
  open Functor F
  module C = Category C
  module D = Category D

  resp-Iso : ∀ {A B} {f : C [ A , B ]} {g : C [ B , A ]}
           → Morphisms.Iso C f g → Morphisms.Iso D (F₁ f) (F₁ g)
  resp-Iso {f = f} {g} I = record
    { isoˡ = begin
               D [ F₁ g ∘ F₁ f ]
             ↑⟨ homomorphism ⟩
               F₁ (C [ g ∘ f ])
             ↓⟨ F-resp-≡ I.isoˡ ⟩
               F₁ (C.id)
             ↓⟨ identity ⟩
               D.id
             ∎
    ; isoʳ = begin
               D [ F₁ f ∘ F₁ g ]
             ↑⟨ homomorphism ⟩
               F₁ (C [ f ∘ g ])
             ↓⟨ F-resp-≡ I.isoʳ ⟩
               F₁ (C.id)
             ↓⟨ identity ⟩
               D.id
             ∎
    }
    where
    module I = Morphisms.Iso I
    open D.HomReasoning

  resp-≅ : F₀ Preserves Morphisms._≅_ C ⟶ Morphisms._≅_ D
  resp-≅ I = record
    { f = F₁ I.f
    ; g = F₁ I.g
    ; iso = resp-Iso I.iso
    }
    where
    module I = Morphisms._≅_ I
