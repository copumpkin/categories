{-# OPTIONS --universe-polymorphism #-}
module Categories.Colimit where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Functor.Constant
open import Categories.Cocones
open import Categories.Cocone
open import Categories.Object.Initial

-- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
record Colimit {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    initial : Initial (Cocones F)
  
  module I = Initial initial
  module Ic = Cocone I.⊥
  private module C = Category C

  ∃F : C.Obj
  ∃F = Ic.N

  ι : NaturalTransformation F (Constant ∃F)  
  ι = record { η = Ic.ψ; commute = λ f → C.Equiv.trans (C.Equiv.sym (Ic.commute f)) (C.Equiv.sym C.identityˡ) }
  
  <_> : ∀ {Q} → NaturalTransformation F (Constant Q) → ∃F C.⇒ Q
  <_> {Q} η = CoconeMorphism.f (I.! {record 
          { N = Q
          ; ψ = η.η
          ; commute = λ f → C.Equiv.trans (C.Equiv.sym C.identityˡ) (C.Equiv.sym (η.commute f)) }}) 
    where
      module η = NaturalTransformation η
    
record Cocomplete (o ℓ e : Level) {o′ ℓ′ e′} (C : Category o′ ℓ′ e′) : Set (suc o ⊔ suc ℓ ⊔ suc e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    colimit : ∀ {J : Category o ℓ e} (F : Functor J C) → Colimit F
