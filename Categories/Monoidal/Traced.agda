{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Traced where

open import Level

open import Categories.Category
open import Categories.Monoidal
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₁_; _≡_; id)

record Traced {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} {B : Braided M}
  (S : Symmetric B) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  private module M = Monoidal M
  private module B = Braided B
  private module S = Symmetric S
  private module MH = MonoidalHelperFunctors C M.⊗ M.id

  field
    -- trace(x,a,b) : C(A⊗X , B⊗X) → C(A,B)
    trace : {X A B : C.Obj} → C [ {!!} , {!!} ] → C [ A , B ]

    -- vanishing: let f : a ⊗ x ⊗ y → b ⊗ x ⊗ y
    --   trace(id,a,b)(f) = f
    --   trace(x⊗y,a,b)=trace(x,a,b)(trace(y,a⊗x,b⊗x)(f))

    -- superposing: let f : a ⊗ x → b ⊗ x
    --   trace(x,c⊗a,c⊗b)(id⊗f) = id ⊗ trace(x,a,b)(f)

    -- yanking
    --   trace(x,x,x)(symmetry_x,x) = id

{--
From: http://ncatlab.org/nlab/show/traced+monoidal+category

A symmetric monoidal category (C,⊗,1,b) (where b is the symmetry) is
said to be traced if it is equipped with a natural family of functions

TrXA,B:C(A⊗X,B⊗X)→C(A,B)
satisfying three axioms:

Vanishing: Tr1A,B(f)=f (for all f:A→B) and
TrX⊗YA,B=TrXA,B(TrYA⊗X,B⊗X(f)) (for all f:A⊗X⊗Y→B⊗X⊗Y)

Superposing: TrXC⊗A,C⊗B(idC⊗f)=idC⊗TrXA,B(f) (for all f:A⊗X→B⊗X)

Yanking: TrXX,X(bX,X)=idX
--}
