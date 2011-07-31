{-# OPTIONS --universe-polymorphism #-}
open import Level
open import Categories.Category
module Categories.Power.NaturalTransformation {o ℓ e : Level} (C : Category o ℓ e) where

open import Function using () renaming (_∘_ to _∙_)
open import Data.Nat using (_+_)
open import Data.Fin using (Fin; inject+; raise)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Product using (_,_)

open import Categories.Support.PropositionalEquality

import Categories.Power
module Pow = Categories.Power C
open Pow public
open import Categories.Bifunctor using (Bifunctor)
open import Categories.Bifunctor.NaturalTransformation renaming (id to idⁿ; _≡_ to _≡ⁿ_)
open import Categories.Functor using (module Functor)

private module C = Category C

flattenPⁿ : ∀ {D : Category o ℓ e} {n m} {F G : Powerfunctor′ D (Fin n ⊎ Fin m)} (η : NaturalTransformation F G) → NaturalTransformation (flattenP F) (flattenP G)
flattenPⁿ {n = n} {m} η = record
  { η = λ Xs → η.η (Xs ∙ pack)
  ; commute = λ fs → η.commute (fs ∙ pack)
  }
  where
  private module η = NaturalTransformation η
  pack = [ inject+ m , raise n ]′

reduceN′ : ∀ (H : Bifunctor C C C) {I} {F F′ : Powerendo′ I} (φ : NaturalTransformation F F′) {J} {G G′ : Powerendo′ J} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce′ H F G) (reduce′ H F′ G′)
reduceN′ H {I} {F} {F′} φ {J} {G} {G′} γ = record
  { η = my-η
  ; commute = λ {Xs Ys} → my-commute Xs Ys
  }
  where
  module F = Functor F
  module F′ = Functor F′
  module G = Functor G
  module G′ = Functor G′
  module φ = NaturalTransformation φ
  module γ = NaturalTransformation γ
  module H = Functor H
  module L = Functor (reduce′ H F G)
  module R = Functor (reduce′ H F′ G′)
  my-η : ∀ Xs → C [ L.F₀ Xs , R.F₀ Xs ]
  my-η Xs = H.F₁ ((φ.η (Xs ∙ inj₁)) , (γ.η (Xs ∙ inj₂)))
  .my-commute : ∀ Xs Ys fs → C.CommutativeSquare (L.F₁ fs) (my-η Xs) (my-η Ys) (R.F₁ fs)
  my-commute Xs Ys fs = begin
      my-η Ys ∘ L.F₁ fs
    ↑⟨ H.homomorphism ⟩
      H.F₁ ((φ.η (Ys ∙ inj₁) ∘ F.F₁ (fs ∙ inj₁)) , (γ.η (Ys ∙ inj₂) ∘ G.F₁ (fs ∙ inj₂)))
    ↓⟨ H.F-resp-≡ ((φ.commute (fs ∙ inj₁)) , (γ.commute (fs ∙ inj₂))) ⟩
      H.F₁ ((F′.F₁ (fs ∙ inj₁) ∘ φ.η (Xs ∙ inj₁)) , (G′.F₁ (fs ∙ inj₂) ∘ γ.η (Xs ∙ inj₂)))
    ↓⟨ H.homomorphism ⟩
      R.F₁ fs ∘ my-η Xs
    ∎
    where
    open C using (_∘_; _≡_)
    open C.HomReasoning

reduceN : ∀ (H : Bifunctor C C C) {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {m} {G G′ : Powerendo m} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce H F G) (reduce H F′ G′)
reduceN H F G = flattenPⁿ (reduceN′ H F G)

overlapN : ∀ (H : Bifunctor C C C) {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {G G′ : Powerendo n} (γ : NaturalTransformation G G′) → NaturalTransformation (overlap {C} {C} H F G) (overlap {C} {C} H F′ G′)
overlapN H F G = overlapN-× {D₁ = C} {D₂ = C} H F G

widenNˡ : ∀ {n} l → {F G : Powerendo n} → NaturalTransformation F G → NaturalTransformation (widenˡ l F) (widenˡ l G)
widenNˡ l {F} {G} φ = record
  { η = λ X → φ.η (λ x → X (raise l x))
  ; commute = λ f → φ.commute (λ i → f (raise l i))
  }
  where
  module φ = NaturalTransformation φ

widenNʳ : ∀ {n} r → {F G : Powerendo n} → NaturalTransformation F G → NaturalTransformation (widenʳ r F) (widenʳ r G)
widenNʳ l {F} {G} φ = record
  { η = λ X → φ.η (λ x → X (inject+ l x))
  ; commute = λ f → φ.commute (λ i → f (inject+ l i))
  }
  where
  module φ = NaturalTransformation φ

overlapN-∘ʳ : ∀ (H : Bifunctor C C C) {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {G G′ : Powerendo n} (γ : NaturalTransformation G G′) {m} (K : Hyperendo m n) → overlapN H φ γ ∘ʳ K ≣ overlapN H (φ ∘ʳ K) (γ ∘ʳ K)
overlapN-∘ʳ H φ γ K = ≣-refl