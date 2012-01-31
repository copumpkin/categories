{-# OPTIONS --universe-polymorphism #-}
module Categories.Graphs.Underlying where

open import Categories.Support.PropositionalEquality

open import Categories.Category
  hiding (module Heterogeneous)
open import Categories.Categories
open import Categories.Graphs
open import Categories.Functor
  using (Functor; module Functor; ≡⇒≣)
  renaming (id to idF; _≡_ to _≡F_)
open import Data.Product
open import Graphs.Graph
open import Graphs.GraphMorphism

Underlying₀ : ∀ {o ℓ e} → Category o ℓ e → Graph o ℓ e
Underlying₀ C = record
  { Obj   = Obj
  ; _↝_   = _⇒_
  ; _≈_   = _≡_
  ; equiv = equiv
  } where open Category C

Underlying₁ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
  {X : Category o₁ ℓ₁ e₁}
  {Y : Category o₂ ℓ₂ e₂}
  → Functor X Y
  → GraphMorphism (Underlying₀ X) (Underlying₀ Y)
Underlying₁ G = record
  { F₀        = G₀
  ; F₁        = G₁
  ; F-resp-≈  = G-resp-≡
  }
  where
    open Functor G
      renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)

Underlying : ∀ {o ℓ e} → Functor (Categories o ℓ e) (Graphs o ℓ e)
Underlying {o}{ℓ}{e} = record
  { F₀            = Underlying₀ 
  ; F₁            = Underlying₁
  ; identity      = (λ x → ≣-refl) , (λ f → Heterogeneous.refl _)
  ; homomorphism  = (λ x → ≣-refl) , (λ f → Heterogeneous.refl _)
  ; F-resp-≡      = λ {A B}{F G : Functor A B} → F-resp-≡ {A}{B}{F}{G}
  }
  where
    module Graphs     = Category (Graphs     o ℓ e)
    module Categories = Category (Categories o ℓ e)
    
    .F-resp-≡ : ∀ {A B : Categories.Obj} {G H : Functor A B}
      → G ≡F H
      → Underlying₁ G ≈ Underlying₁ H
    F-resp-≡ {A}{B}{G}{H} G≡H
      = (≡⇒≣ G H G≡H) , (λ f → convert-~ (G≡H f))
      where
        open Heterogeneous (Underlying₀ B)
          renaming (_~_ to _~₂_)
        open Categories.Category.Heterogeneous B
          renaming (_∼_ to _~₁_)
        
        convert-~ : ∀ {a b c d}{x : B [ a , b ]}{y : B [ c , d ]} → x ~₁ y → x ~₂ y
        convert-~ (≡⇒∼ foo) = ≈⇒~ foo