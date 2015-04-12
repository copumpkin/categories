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

record Polarized {o o' : Level} (A : Set o) (B : Set o') : Set (o ⊔ o') where
  constructor ±
  field
    pos : A
    neg : B

IntC : ∀ {o ℓ e}
       {C : Category o ℓ e} {M : Monoidal C} {B : Braided M} {S : Symmetric B} →
       (T : Traced S) → Category o ℓ e
IntC {o} {ℓ} {e} {C} {M} {B} {S} T = record {
    Obj = Polarized C.Obj C.Obj
  ; _⇒_ = λ { (± A+ A-) (± B+ B-) → C [ F.⊗ₒ (A+ , B-) , F.⊗ₒ (B+ , A-) ]}
  ; _≡_ = C._≡_
  ; _∘_ = λ { {(± A+ A-)} {(± B+ B-)} {(± C+ C-)} g f →
            T.trace { B- } {F.⊗ₒ (A+ , C-)} {F.⊗ₒ (C+ , A-)}
              (ηassoc⇐ (ternary C C+ A- B-) C.∘
               F.⊗ₘ (C.id , ηbraid (binary C B- A-)) C.∘
               ηassoc⇒ (ternary C C+ B- A-) C.∘
               F.⊗ₘ (g , C.id) C.∘
               ηassoc⇐ (ternary C B+ C- A-) C.∘
               F.⊗ₘ (C.id , ηbraid (binary C A- C-)) C.∘
               ηassoc⇒ (ternary C B+ A- C-) C.∘
               F.⊗ₘ (f , C.id) C.∘
               ηassoc⇐ (ternary C A+ B- C-) C.∘
               F.⊗ₘ (C.id , ηbraid (binary C C- B-)) C.∘
               ηassoc⇒ (ternary C A+ C- B-))}
  ; id = F.⊗ₘ (C.id , C.id)
  ; assoc = λ { {(± A+ A-)} {(± B+ B-)} {(± C+ C-)} {(± D+ D-)} {f} {g} {h} →
            {!!} }
  ; identityˡ = λ { {(± A+ A-)} {(± B+ B-)} {f} →
                (begin
                  {!!}
                ↓⟨ {!!} ⟩ 
                  f ∎) }
  ; identityʳ = λ { {(± A+ A-)} {(± B+ B-)} {f} →
                {!!} }
  ; equiv = C.equiv
  ; ∘-resp-≡ = λ { {(± A+ A-)} {(± B+ B-)} {(± C+ C-)} {f} {h} {g} {i} f≡h g≡i →
               {!!} }
  }
  where
    module C = Category C
    open C.HomReasoning
    module M = Monoidal M renaming (id to 𝟙)
    module F = Functor M.⊗ renaming (F₀ to ⊗ₒ; F₁ to ⊗ₘ)
    module B = Braided B
    module S = Symmetric S
    module T = Traced T
    module NIassoc = NaturalIsomorphism M.assoc
    open NaturalTransformation NIassoc.F⇒G renaming (η to ηassoc⇒)
    open NaturalTransformation NIassoc.F⇐G renaming (η to ηassoc⇐)
    module NIbraid = NaturalIsomorphism B.braid
    open NaturalTransformation NIbraid.F⇒G renaming (η to ηbraid)

IntConstruction : ∀ {o ℓ e}
  {C : Category o ℓ e} {M : Monoidal C} {B : Braided M} {S : Symmetric B} →
  (T : Traced S) →
  Σ[ IntC ∈ Category o ℓ e ]
  Σ[ MIntC ∈ Monoidal IntC ]
  Σ[ BIntC ∈ Braided MIntC ]
  Σ[ SIntC ∈ Symmetric BIntC ]
  Traced SIntC
IntConstruction = {!!} 
    

