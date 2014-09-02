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
record Colimit {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} (F : Functor J C) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    initial : Initial (Cocones F)
  
  module I = Initial (Cocones F) initial
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
    
record Cocomplete (o a : Level) {o′ a′} (C : Category o′ a′) : Set (suc o ⊔ suc a ⊔ o′ ⊔ a′) where
  field
    colimit : ∀ {J : Category o a} (F : Functor J C) → Colimit F
