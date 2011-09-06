{-# OPTIONS --universe-polymorphism #-}
module Categories.Cone where

open import Level
open import Relation.Binary using (IsEquivalence; Setoid; module Setoid)

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor hiding (_≡_; _∘_)

module ConeOver {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where
  module J = Category J
  open Category C
  open Functor F
  record Cone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    field
      N : Obj
      ψ : ∀ X → (N ⇒ (F₀ X))
      .commute : ∀ {X Y} (f : J [ X , Y ]) → F₁ f ∘ ψ X ≡ ψ Y

  record _≜_ (X Y : Cone) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    module X = Cone X
    module Y = Cone Y
    field
      N-≣ : X.N ≣ Y.N
      ψ-≡ : ∀ j → C [ X.ψ j ∼ Y.ψ j ]

  ≜-is-equivalence : IsEquivalence _≜_
  ≜-is-equivalence = record
    { refl = record { N-≣ = ≣-refl; ψ-≡ = λ j → refl }
    ; sym = λ X≜Y → let module X≜Y = _≜_ X≜Y in record
      { N-≣ = ≣-sym X≜Y.N-≣
      ; ψ-≡ = λ j → sym (X≜Y.ψ-≡ j)
      }
    ; trans = λ X≜Y Y≜Z → 
      let module X≜Y = _≜_ X≜Y in
      let module Y≜Z = _≜_ Y≜Z in
      record
        { N-≣ = ≣-trans X≜Y.N-≣ Y≜Z.N-≣
        ; ψ-≡ = λ j → trans (X≜Y.ψ-≡ j) (Y≜Z.ψ-≡ j)
        }
    }
    where open Heterogeneous C

  cone-setoid : Setoid _ _
  cone-setoid = record
    { Carrier = Cone
    ; _≈_ = _≜_
    ; isEquivalence = ≜-is-equivalence
    }

  open Setoid cone-setoid public renaming (refl to ≜-refl; sym to ≜-sym; trans to ≜-trans; reflexive to ≜-reflexive)

open ConeOver public using (Cone; cone-setoid)