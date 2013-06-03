{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Product where

open import Data.Product using (uncurry′)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.Object.BinaryProducts using (BinaryProducts; module BinaryProducts)

-- Ugh, we should start bundling things (categories with binary products, in this case) up consistently
module ProductFunctors {o a} (C : Category o a) (BP : BinaryProducts C) where
  open Category C
  open BinaryProducts C BP

  ─×─ : Bifunctor C C C
  ─×─ = record
    { F₀ = uncurry′ _×_
    ; F₁ = uncurry′ _⁂_
    ; identity = universal (id-comm {f = π₁}) (id-comm {f = π₂})
    ; homomorphism = Equiv.sym ⁂∘⁂
    }

  _×─ : Obj → Functor C C
  O ×─ = record
    { F₀ = _×_ O
    ; F₁ = second
    ; identity = universal (id-comm {f = π₁}) (id-comm {f = π₂})
    ; homomorphism = Equiv.sym second∘second
    }

  ─×_ : Obj → Functor C C
  ─× O = record
   { F₀ = λ X → X × O
   ; F₁ = first
   ; identity = universal (id-comm {f = π₁}) (id-comm {f = π₂})
   ; homomorphism = Equiv.sym first∘first
   }

open ProductFunctors public using () renaming ( ─×─ to _[_][-×-]
                                              ; _×─ to _[_][_×-]
                                              ; ─×_ to _[_][-×_] )
