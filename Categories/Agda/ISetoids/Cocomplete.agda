{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda.ISetoids.Cocomplete where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)
open import Data.Product using (Σ; _,_)
-- import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Support.Equivalence using (module I→R-Wrapper; setoid-i→r) renaming (Setoid to ISetoid; module Setoid to ISetoid)
open import Categories.Support.SetoidFunctions using (module _⟶_)
open import Categories.Support.PropositionalEquality
import Categories.Support.ZigZag as ZigZag

open import Categories.Category
open import Categories.Functor
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone
open import Categories.Agda.ISetoids.Cocomplete.Helpers

open I→R-Wrapper

ISetoidsCocomplete : ∀ {o ℓ e c ℓ′} → Cocomplete o ℓ e (ISetoids (c ⊔ ding (o ⊔ ℓ ⊔ e)) (c ⊔ ℓ′ ⊔ ding (o ⊔ ℓ ⊔ e)))
ISetoidsCocomplete {o} {ℓ} {e} {c} {cℓ} = record { colimit = colimit }
  where
  c′ = c ⊔ ding (o ⊔ ℓ ⊔ e)
  ℓ′ = c ⊔ cℓ ⊔ ding (o ⊔ ℓ ⊔ e)
  C = ISetoids c′ ℓ′
  colimit : ∀ {J : Category o ℓ e} (F : Functor J C) → Colimit F
  colimit {J} F = record { initial = my-initial-cocone }
    where
    module J = Category J
    open Functor F
    open ISetoid
    open _⟶_

    open ColimitCocone {c = c} {cℓ} {J} F

    .my-!-unique : (A : Cocone F) (φ : CoconeMorphism ⊥ A) (x : vertex-carrier) → (_≈_ (Cocone.N A) (CoconeMorphism.f (! {A}) ⟨$⟩ x) (CoconeMorphism.f φ ⟨$⟩ x))
    my-!-unique A φ (X , x) = sym (Cocone.N A) (CoconeMorphism.commute φ (refl (F₀ X)))

    my-initial-cocone : Initial (Cocones F)
    my-initial-cocone = record
      { ⊥ = ⊥
      ; ! = !
      ; !-unique = λ {A} φ {x} {y} x≡y → trans (Cocone.N A) (my-!-unique A φ x) (cong (CoconeMorphism.f φ) x≡y)
      }