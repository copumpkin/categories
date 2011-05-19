{-# OPTIONS --universe-polymorphism #-}
open import Support using (Level)
open import Category using (Category)
module Category.Power.NaturalTransformation {o ℓ e : Level} (C : Category o ℓ e) where

import Category.Power
module Pow = Category.Power C
open Pow public
open import Support
open import Support.Nat
open import Support.FinSet
open import Category
open import Category.Bifunctor using (Bifunctor)
open import Category.NaturalTransformation renaming (id to idⁿ; _≡_ to _≡ⁿ_)
import Category.Functor

flattenPⁿ : ∀ {D : Category o ℓ e} {n m} {F G : Powerfunctor′ D (Either (Fin n) (Fin m))} (η : NaturalTransformation F G) → NaturalTransformation (flattenP F) (flattenP G)
flattenPⁿ {n = n} {m} η = record
  { η = λ Xs → η.η (Xs ∙ pack)
  ; commute = λ fs → η.commute (fs ∙ pack)
  }
  where
  private module η = Category.NaturalTransformation.NaturalTransformation η
  pack = either₀ (widen-+ m) (shift n)

reduceN′ : ∀ (H : Bifunctor C C C) {I} {F F′ : Powerendo′ I} (φ : NaturalTransformation F F′) {J} {G G′ : Powerendo′ J} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce′ H F G) (reduce′ H F′ G′)
reduceN′ H {I} {F} {F′} φ {J} {G} {G′} γ = record
  { η = my-η
  ; commute = λ {Xs Ys} → my-commute Xs Ys
  }
  where
  module F = Category.Functor.Functor F
  module F′ = Category.Functor.Functor F′
  module G = Category.Functor.Functor G
  module G′ = Category.Functor.Functor G′
  module φ = Category.NaturalTransformation.NaturalTransformation φ
  module γ = Category.NaturalTransformation.NaturalTransformation γ
  module H = Category.Functor.Functor H
  module L = Category.Functor.Functor (reduce′ H F G)
  module R = Category.Functor.Functor (reduce′ H F′ G′)
  my-η : ∀ Xs → C [ L.F₀ Xs , R.F₀ Xs ]
  my-η Xs = H.F₁ ((φ.η (Xs ∙ inl)) , (γ.η (Xs ∙ inr)))
  .my-commute : ∀ Xs Ys fs → C.CommutativeSquare (L.F₁ fs) (my-η Xs) (my-η Ys) (R.F₁ fs)
  my-commute Xs Ys fs = begin
      my-η Ys ∘ L.F₁ fs
    ≈⟨ sym H.homomorphism ⟩
      H.F₁ ((φ.η (Ys ∙ inl) ∘ F.F₁ (fs ∙ inl)) , (γ.η (Ys ∙ inr) ∘ G.F₁ (fs ∙ inr)))
    ≈⟨ H.F-resp-≡ ((φ.commute (fs ∙ inl)) , (γ.commute (fs ∙ inr))) ⟩
      H.F₁ ((F′.F₁ (fs ∙ inl) ∘ φ.η (Xs ∙ inl)) , (G′.F₁ (fs ∙ inr) ∘ γ.η (Xs ∙ inr)))
    ≈⟨ H.homomorphism ⟩
      R.F₁ fs ∘ my-η Xs
    ∎
    where
    open C using (_∘_; _≡_)
    open C.Equiv
    open SetoidReasoning C.hom-setoid

reduceN : ∀ (H : Bifunctor C C C) {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {m} {G G′ : Powerendo m} (γ : NaturalTransformation G G′) → NaturalTransformation (reduce H F G) (reduce H F′ G′)
reduceN H F G = flattenPⁿ (reduceN′ H F G)

