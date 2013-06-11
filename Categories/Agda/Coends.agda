module Categories.Agda.Coends where

open import Level
open import Data.Product
open import Data.Star
import      Function as Fn
open        Fn using (_∘′_) renaming (_∘_ to _∙_)
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence using (set→setoid)
open import Categories.Support.EqReasoning using (module SetoidReasoning)
open import Categories.Support.Quotients
import      Categories.Support.ZigZag as ZigZag
open import Categories.Support.IProduct using (Σ′; _,_)

open import Categories.Category
open import Categories.Product using () renaming (Product to _×ᶜ_)
open import Categories.Bifunctor
open import Categories.Functor using (module Functor)
open import Categories.Agda
open import Categories.Coend
open import Categories.Coequalizer
open import Categories.Agda.Coequalizers

coend : ∀ {o a ℓ} {C : Category o a} (F : Bifunctor (Category.op C) C (Sets (ℓ ⊔ a ⊔ o))) → Coend {C = C} F
coend {o} {a} {ℓ} {C} F = record
  { Data = record
    { E = K.vertex
    ; π = record
      { α = λ c → K.arr ∘′ _,_ c
      ; commute = λ f → ≣-cong (λ g → g ∘′ ,_ ∘′ ,_ ∘′ _,_ f) K.commute
      }
    }
  ; universal = λ Q → let module Q = Coend-data Q in
                      K.factor (uncurry Q.π.α) (lifted-commute Q)
  ; universal∘π[c]≡δ[c] = λ {Q} c → let module Q = Coend-data Q in
                          ≣-cong (λ g → g ∘′ _,_ c)
                                 (K.factored (uncurry Q.π.α) (lifted-commute Q))
  ; universal-unique = λ {Q} → let module Q = Coend-data Q in λ u eqs →
                       ≣-sym (K.universal (uncurry Q.π.α)
                                          (lifted-commute Q)
                                          u
                                          (≣-cong uncurry (≣-ext eqs)))
  }
  module coend where
    module F = Functor F
    open F
    module C = Category C

    rawCarrier : Set (o ⊔ ℓ ⊔ a)
    rawCarrier = ∃ λ c → F₀ (c , c)

    rawRelator : Set (o ⊔ a ⊔ ℓ)
    rawRelator = ∃₂ λ c₁ c₂ → C [ c₂ , c₁ ] × F₀ (c₁ , c₂)

    leftAction : rawRelator → rawCarrier
    leftAction (_ , _ , f , x) = , F₁ (C.id , f) x

    rightAction : rawRelator → rawCarrier
    rightAction (_ , _ , f , x) = , F₁ (f , C.id) x

    coequalizer : Coequalizer (Sets (ℓ ⊔ o ⊔ a)) leftAction rightAction
    coequalizer = coeq leftAction rightAction

    module K = Coequalizer _ coequalizer

    module _ (Q : Coend-data F) where
      private module Q = Coend-data Q

      .lifted-commute : uncurry Q.π.α ∘′ leftAction ≣ uncurry Q.π.α ∘′ rightAction
      lifted-commute = (≣-cong uncurry  ∙ ≣-ext) λ c  → 
                       (≣-cong uncurry  ∙ ≣-ext) λ c′ → 
                       (≣-cong uncurry′ ∙ ≣-ext) λ f  → 
                                          ≣-ext  λ x  → ≣-app (Q.π.commute f) x
{-
      lifted-commute = {!≣-cong uncurry (≣-ext λ c →
                       ≣-cong uncurry (≣-ext λ c′ →
                       ≣-cong uncurry (≣-ext Q.π.commute)))!}
-}
