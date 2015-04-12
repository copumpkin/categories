{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Traced where

open import Level

open import Data.Product
open import Data.Fin

open import Categories.Category
open import Categories.Monoidal
open import Categories.Functor hiding (id; _∘_; identityʳ; assoc)
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation hiding (id)
  
------------------------------------------------------------------------------
-- Helpers

unary : ∀ {o ℓ e} → (C : Category o ℓ e) → (A : Category.Obj C) →
          Fin 1 → Category.Obj C
unary C A zero = A
unary C A (suc ())

binary : ∀ {o ℓ e} → (C : Category o ℓ e) → (A B : Category.Obj C) →
          Fin 2 → Category.Obj C
binary C A B zero = A
binary C A B (suc zero) = B
binary C A B (suc (suc ()))

ternary : ∀ {o ℓ e} → (C : Category o ℓ e) → (A X Y : Category.Obj C) →
          Fin 3 → Category.Obj C
ternary C A X Y zero = A
ternary C A X Y (suc zero) = X
ternary C A X Y (suc (suc zero)) = Y
ternary C A X Y (suc (suc (suc ())))

------------------------------------------------------------------------------
-- Def from http://ncatlab.org/nlab/show/traced+monoidal+category
-- 
-- A symmetric monoidal category (C,⊗,1,b) (where b is the symmetry) is
-- said to be traced if it is equipped with a natural family of functions
-- 
-- TrXA,B:C(A⊗X,B⊗X)→C(A,B)
-- satisfying three axioms:
-- 
-- Vanishing: Tr1A,B(f)=f (for all f:A→B) and
-- TrX⊗YA,B=TrXA,B(TrYA⊗X,B⊗X(f)) (for all f:A⊗X⊗Y→B⊗X⊗Y)
-- 
-- Superposing: TrXC⊗A,C⊗B(idC⊗f)=idC⊗TrXA,B(f) (for all f:A⊗X→B⊗X)
-- 
-- Yanking: TrXX,X(bX,X)=idX

record Traced {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} {B : Braided M}
  (S : Symmetric B) : Set (o ⊔ ℓ ⊔ e) where

  private module C = Category C
  open C using (Obj; id; _∘_)

  private module M = Monoidal M
  open M using (⊗; identityʳ; assoc) renaming (id to 𝟙)

  private module F = Functor ⊗
  open F using () renaming (F₀ to ⊗ₒ; F₁ to ⊗ₘ)

  private module NIʳ = NaturalIsomorphism identityʳ
  open NaturalTransformation NIʳ.F⇒G renaming (η to ηidr⇒)
  open NaturalTransformation NIʳ.F⇐G renaming (η to ηidr⇐)

  private module NIassoc = NaturalIsomorphism assoc
  open NaturalTransformation NIassoc.F⇒G renaming (η to ηassoc⇒)
  open NaturalTransformation NIassoc.F⇐G renaming (η to ηassoc⇐)

  private module B = Braided B
  open B using (braid)

  private module NIbraid = NaturalIsomorphism braid
  open NaturalTransformation NIbraid.F⇒G renaming (η to ηbraid⇒)

  field
    trace : ∀ {X A B} → C [ ⊗ₒ (A , X)  , ⊗ₒ (B , X) ] → C [ A , B ]

    vanish_id : ∀ {A B f} →
                C [
                    trace {𝟙} {A} {B} f
                  ≡
                    (ηidr⇒ (unary C B) ∘ f ∘ ηidr⇐ (unary C A))
                  ]
                  
    vanish_⊗ : ∀ {X Y A B f} →
               C [
                    trace {⊗ₒ (X , Y)} {A} {B} f
                  ≡
                    trace {X} {A} {B}
                      (trace {Y} {⊗ₒ (A , X)} {⊗ₒ (B , X)}
                        ((ηassoc⇐ (ternary C B X Y)) ∘ f ∘ (ηassoc⇒ (ternary C A X Y))))
                 ]

    superpose : ∀ {X Y A B} {f : C [ ⊗ₒ (A , X) , ⊗ₒ (B , X) ]} → 
                C [
                    trace {X} {⊗ₒ (Y , A)} {⊗ₒ (Y , B)}
                      (ηassoc⇐ (ternary C Y B X) ∘ ⊗ₘ (id , f) ∘ ηassoc⇒ (ternary C Y A X))
                   ≡
                    ⊗ₘ (id , (trace {X} {A} {B} f))
                  ]

    yank : ∀ {X} →
           C [
               trace {X} {X} {X} (ηbraid⇒ (binary C X X)) 
              ≡
               id
             ]

------------------------------------------------------------------------------
