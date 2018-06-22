{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Helpers where

open import Data.Nat using (_+_)
open import Function using (flip)

open import Categories.Category
import Categories.Functor

open import Categories.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)

module MonoidalHelperFunctors {o ℓ e} (C : Category o ℓ e) (—⊗— : Bifunctor C C C) (id : Category.Obj C) where
  private module C = Category C
  open C hiding (id; identityˡ; identityʳ)

  import Categories.Power.NaturalTransformation
  private module PowNat = Categories.Power.NaturalTransformation C
  open PowNat

  private module ⊗ = Functor —⊗— renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  infix 2 _⊗_
  _⊗_ : ∀ {n m} (F : Powerendo n) (G : Powerendo m) → Powerendo (n + m)
  _⊗_ = reduce —⊗—

  _⊗₂_ : ∀ {m} (F G : Powerendo m) → Powerendo m
  _⊗₂_ = overlaps {C} —⊗— -- reduce (flip-bifunctor {C = C} {C} —⊗—)

  id↑ : Powerendo 0
  id↑ = nullary id

  x : Powerendo 1
  x = unary (idF {C = C})

  id⊗x : Powerendo 1
  id⊗x = id↑ ⊗ x

  x⊗id : Powerendo 1
  x⊗id = x ⊗ id↑

  x⊗y : Powerendo 2
  x⊗y = binary —⊗—

  y⊗x : Powerendo 2
  y⊗x = binary (flip-bifunctor {C = C} {C} —⊗—)


  [x⊗y]⊗z : Powerendo 3
  [x⊗y]⊗z = x⊗y ⊗ x

  x⊗[y⊗z] : Powerendo 3
  x⊗[y⊗z] = x ⊗ x⊗y


  
  [y⊗z]⊗x : Powerendo 3
  [y⊗z]⊗x = (select 1 ⊗₂ select 2) ⊗₂ select 0

  [y⊗x]⊗z : Powerendo 3
  [y⊗x]⊗z = (select 1 ⊗₂ select 0) ⊗₂ select 2

  y⊗[x⊗z] : Powerendo 3
  y⊗[x⊗z] = select 1 ⊗₂ (select 0 ⊗₂ select 2)

  y⊗[z⊗x] : Powerendo 3
  y⊗[z⊗x] = select 1 ⊗₂ (select 2 ⊗₂ select 0)



  z⊗[x⊗y] : Powerendo 3
  z⊗[x⊗y] = select 2 ⊗₂ (select 0 ⊗₂ select 1)

  x⊗[z⊗y] : Powerendo 3
  x⊗[z⊗y] = select 0 ⊗₂ (select 2 ⊗₂ select 1)

  [x⊗z]⊗y : Powerendo 3
  [x⊗z]⊗y = (select 0 ⊗₂ select 2) ⊗₂ select 1

  [z⊗x]⊗y : Powerendo 3
  [z⊗x]⊗y = (select 2 ⊗₂ select 0) ⊗₂ select 1
  
  [x⊗id]⊗y : Powerendo 2
  [x⊗id]⊗y = x⊗id ⊗ x

  x⊗[id⊗y] : Powerendo 2
  x⊗[id⊗y] = x ⊗ id⊗x

  [[x⊗y]⊗z]⊗w : Powerendo 4
  [[x⊗y]⊗z]⊗w = [x⊗y]⊗z ⊗ x
  
  [x⊗y]⊗[z⊗w] : Powerendo 4
  [x⊗y]⊗[z⊗w] = x⊗y ⊗ x⊗y

  x⊗[y⊗[z⊗w]] : Powerendo 4
  x⊗[y⊗[z⊗w]] = x ⊗ x⊗[y⊗z]

  x⊗[[y⊗z]⊗w] : Powerendo 4
  x⊗[[y⊗z]⊗w] = x ⊗ [x⊗y]⊗z

  [x⊗[y⊗z]]⊗w : Powerendo 4
  [x⊗[y⊗z]]⊗w = x⊗[y⊗z] ⊗ x


  infix 2 _⊗ⁿ_
  _⊗ⁿ_ : ∀ {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {m} {G G′ : Powerendo m} (γ : NaturalTransformation G G′) → NaturalTransformation (F ⊗ G) (F′ ⊗ G′)
  _⊗ⁿ_ = reduceN —⊗—

  infix 2 _⊗ⁿ′_
  _⊗ⁿ′_ : ∀ {n} {F F′ : Powerendo n} (φ : NaturalTransformation F F′) {G G′ : Powerendo n} (γ : NaturalTransformation G G′) → NaturalTransformation (F ⊗₂ G) (F′ ⊗₂ G′)
  _⊗ⁿ′_ = overlapN —⊗—


  id₂ : NaturalTransformation x x
  id₂ = idⁿ

  id3 : {F : Powerendo 3} → NaturalTransformation F F
  id3 = idⁿ

  module Coherence (identityˡ : NaturalIsomorphism id⊗x x)
                   (identityʳ : NaturalIsomorphism x⊗id x)
                   (assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]) where
    open NaturalIsomorphism identityˡ using () renaming (F⇒G to υˡ)
    open NaturalIsomorphism identityʳ using () renaming (F⇒G to υʳ)
    open NaturalIsomorphism assoc using () renaming (F⇒G to α)

    α-over : ∀ {n₁ n₂ n₃} (F₁ : Powerendo n₁) (F₂ : Powerendo n₂) (F₃ : Powerendo n₃) → NaturalTransformation ((F₁ ⊗ F₂) ⊗ F₃) (reduce2ʳ —⊗— F₁ F₂ F₃)
    α-over F₁ F₂ F₃ = α ∘ʳ ((hyp F₁ ∥ hyp F₂) ∥ hyp F₃)

    TriangleLeftSide : NaturalTransformation [x⊗id]⊗y x⊗y
    TriangleLeftSide = υʳ ⊗ⁿ id₂

    TriangleTopSide : NaturalTransformation [x⊗id]⊗y x⊗[id⊗y]
    TriangleTopSide = α-over x id↑ x

    TriangleRightSide : NaturalTransformation x⊗[id⊗y] x⊗y
    TriangleRightSide = id₂ ⊗ⁿ υˡ

    PentagonNWSide : NaturalTransformation [[x⊗y]⊗z]⊗w [x⊗y]⊗[z⊗w]
    PentagonNWSide = α-over x⊗y x x

    PentagonNESide : NaturalTransformation [x⊗y]⊗[z⊗w] x⊗[y⊗[z⊗w]]
    PentagonNESide = α-over x x x⊗y

    PentagonSWSide : NaturalTransformation [[x⊗y]⊗z]⊗w [x⊗[y⊗z]]⊗w
    PentagonSWSide = α ⊗ⁿ id₂

    PentagonSSide : NaturalTransformation [x⊗[y⊗z]]⊗w x⊗[[y⊗z]⊗w]
    PentagonSSide = α-over x x⊗y x

    PentagonSESide : NaturalTransformation x⊗[[y⊗z]⊗w] x⊗[y⊗[z⊗w]]
    PentagonSESide = id₂ ⊗ⁿ α
