{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Traced where

open import Level

open import Data.Product

open import Categories.Category
open import Categories.Monoidal
open import Categories.Functor hiding (_∘_)
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation 

record Traced {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} {B : Braided M}
  (S : Symmetric B) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  open C using (Obj; _∘_)
  private module M = Monoidal M
  private module S = Symmetric S

  private module H = MonoidalHelperFunctors C M.⊗ M.id
  private module NIʳ = NaturalIsomorphism M.identityʳ
  
  private module NTʳ⇒ = NaturalTransformation NIʳ.F⇒G
  private module NTʳ⇐ = NaturalTransformation NIʳ.F⇐G

  private module F = Functor M.⊗
  open F using () renaming (F₀ to ⊗)

  field
    trace : {X A B : Obj} → C [ ⊗ (A , X)  , ⊗ (B , X) ] → C [ A , B ]

    vanish_id : {A B : Obj} {f : C [ ⊗ (A , M.id) , ⊗ (B , M.id) ]} →
                C [ trace {M.id} {A} {B} f ≡ (NTʳ⇒.η (λ i → B) ∘ f ∘ NTʳ⇐.η (λ i → A)) ]


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
