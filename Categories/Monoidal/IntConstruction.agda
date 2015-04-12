{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.IntConstruction where

open import Level

open import Data.Fin
open import Data.Product

open import Categories.Category
open import Categories.Product
open import Categories.Monoidal
open import Categories.Functor hiding (id; _∘_; identityʳ; assoc)
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Helpers
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation hiding (id)
open import Categories.Monoidal.Traced
  
------------------------------------------------------------------------------

IntC : ∀ {o ℓ e}
       {C : Category o ℓ e} {M : Monoidal C} {B : Braided M} {S : Symmetric B} →
       (T : Traced S) → Category o ℓ e
IntC {o} {ℓ} {e} {C} {M} {B} {S} T = record {
    Obj = C.Obj × C.Obj
  ; _⇒_ = λ { (A+ , A-) (B+ , B-) → C [ F.F₀ (A+ , B-) , F.F₀ (B+ , A-) ]}
  ; _≡_ = {!!}
  ; _∘_ = λ { {(A+ , A-)} {(B+ , B-)} {(C+ , C-)} g f →
            T.trace { B- } {F.F₀ (A+ , C-)} {F.F₀ (C+ , A-)} {!!} }
  ; id = F.F₁ (C.id , C.id)
  ; assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; equiv = {!!}
  ; ∘-resp-≡ = {!!}
  }
  where
    module C = Category C
    module M = Monoidal M
    module F = Functor M.⊗
    module B = Braided B
    module S = Symmetric S
    module T = Traced T
    

IntConstruction : ∀ {o ℓ e}
  {C : Category o ℓ e} {M : Monoidal C} {B : Braided M} {S : Symmetric B} →
  (T : Traced S) →
  Σ[ IntC ∈ Category o ℓ e ]
  Σ[ MIntC ∈ Monoidal IntC ]
  Σ[ BIntC ∈ Braided MIntC ]
  Σ[ SIntC ∈ Symmetric BIntC ]
  Traced SIntC
IntConstruction = {!!} 
    

