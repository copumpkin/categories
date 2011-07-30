{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Braided.Helpers where

open import Categories.Monoidal.Helpers

open import Data.Nat using (_+_)
open import Function using (flip)

open import Categories.Category
import Categories.Functor

open import Categories.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)

module BraidedHelperFunctors {o ℓ e} (C : Category o ℓ e) (—⊗— : Bifunctor C C C) (id : Category.Obj C) where
  open MonoidalHelperFunctors C —⊗— id
  
  private module C = Category C
  open C hiding (id; identityˡ; identityʳ)

  import Categories.Power.NaturalTransformation
  private module PowNat = Categories.Power.NaturalTransformation C
  open PowNat

  private module ⊗ = Functor —⊗— renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  module Braiding (identityˡ : NaturalIsomorphism id⊗x x)
                  (identityʳ : NaturalIsomorphism x⊗id x)
                  (assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z])
                  (braid : NaturalIsomorphism x⊗y y⊗x) where
    open NaturalIsomorphism identityˡ using () renaming (F⇒G to υˡ)
    open NaturalIsomorphism identityʳ using () renaming (F⇒G to υʳ)
    open NaturalIsomorphism assoc using () renaming (F⇒G to α; F⇐G to α₂)
    open NaturalIsomorphism braid using () renaming (F⇒G to B)


    
    α-over : ∀ {n} (F₁ F₂ F₃ : Powerendo n) → NaturalTransformation ((F₁ ⊗₂ F₂) ⊗₂ F₃) (overlap2ʳ —⊗— F₁ F₂ F₃)
    α-over F₁ F₂ F₃ = α ∘ʳ plex {3} F₁ F₂ F₃ -- ((hyp F₁ ∥ hyp F₂) ∥ hyp F₃)

    α₂-over : ∀ {n} (F₁ F₂ F₃ : Powerendo n) → NaturalTransformation (overlap2ʳ —⊗— F₁ F₂ F₃) ((F₁ ⊗₂ F₂) ⊗₂ F₃)
    α₂-over F₁ F₂ F₃ = α₂ ∘ʳ plex {3} F₁ F₂ F₃

    B-over : ∀ {n} (F₁ F₂ : Powerendo n) → NaturalTransformation (F₁ ⊗₂ F₂) (F₂ ⊗₂ F₁)
    B-over F₁ F₂ = B ∘ʳ plex {2} F₁ F₂

    BTriangleTop   : NaturalTransformation id⊗x x⊗id
    BTriangleTop   = B-over (widenˡ 1 id↑) x

    BTriangleLeft  : NaturalTransformation id⊗x x
    BTriangleLeft  = υˡ
    
    BTriangleRight : NaturalTransformation x⊗id x
    BTriangleRight = υʳ


    Hexagon1TopA    : NaturalTransformation [x⊗y]⊗z x⊗[y⊗z]
    Hexagon1TopA    = α-over (select 0) (select 1) (select 2)
    Hexagon1TopB    : NaturalTransformation x⊗[y⊗z] [y⊗z]⊗x
    Hexagon1TopB    = B-over (select 0) (select 1 ⊗₂ select 2)
    Hexagon1SideB   : NaturalTransformation [y⊗z]⊗x y⊗[z⊗x]
    Hexagon1SideB   = α-over (select 1) (select 2) (select 0)

    Hexagon1SideA   : NaturalTransformation [x⊗y]⊗z [y⊗x]⊗z
    Hexagon1SideA   = B-over (select 0) (select 1) ⊗ⁿ′ id3 {select 2}
    Hexagon1BottomA : NaturalTransformation [y⊗x]⊗z y⊗[x⊗z]
    Hexagon1BottomA = α-over (select 1) (select 0) (select 2)
    Hexagon1BottomB : NaturalTransformation y⊗[x⊗z] y⊗[z⊗x]
    Hexagon1BottomB = id3 {select 1} ⊗ⁿ′ B-over (select 0) (select 2)

    Hexagon2TopA    : NaturalTransformation x⊗[y⊗z] [x⊗y]⊗z
    Hexagon2TopA    = α₂-over (select 0) (select 1) (select 2)
    Hexagon2TopB    : NaturalTransformation [x⊗y]⊗z z⊗[x⊗y]
    Hexagon2TopB    = B-over (select 0 ⊗₂ select 1) (select 2)
    Hexagon2SideB   : NaturalTransformation z⊗[x⊗y] [z⊗x]⊗y
    Hexagon2SideB   = α₂-over (select 2) (select 0) (select 1)

    Hexagon2SideA   : NaturalTransformation x⊗[y⊗z] x⊗[z⊗y]
    Hexagon2SideA   = id3 {select 0} ⊗ⁿ′ B-over (select 1) (select 2)
    Hexagon2BottomA : NaturalTransformation x⊗[z⊗y] [x⊗z]⊗y
    Hexagon2BottomA = α₂-over (select 0) (select 2) (select 1)
    Hexagon2BottomB : NaturalTransformation [x⊗z]⊗y [z⊗x]⊗y
    Hexagon2BottomB = B-over (select 0) (select 2) ⊗ⁿ′ id3 {select 1}
