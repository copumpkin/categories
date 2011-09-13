{-# OPTIONS --universe-polymorphism #-}
module Categories.Graphs.Underlying where

open import Categories.Category
  hiding (module Heterogeneous)
open import Categories.Categories
open import Categories.Graphs
open import Categories.Functor
  using (Functor; module Functor)
  renaming (id to idF; _≡_ to _≡F_)
open import Graphs.Graph
open import Graphs.GraphMorphism

Underlying : ∀ {o ℓ e} → Functor (Categories o ℓ e) (Graphs o ℓ e)
Underlying {o}{ℓ}{e} = record
  { F₀            = F₀ 
  ; F₁            = F₁
  ; identity      = λ f → Heterogeneous.refl _
  ; homomorphism  = λ f → Heterogeneous.refl _
  ; F-resp-≡      = λ {A B}{F G : Functor A B} → F-resp-≡ {A}{B}{F}{G}
  }
  where
    module Graphs     = Category (Graphs     o ℓ e)
    module Categories = Category (Categories o ℓ e)
    
    F₀ : Category o ℓ e → Graph o ℓ e
    F₀ C = record
      { Obj   = Obj
      ; _↝_   = _⇒_
      ; _≈_   = _≡_
      ; equiv = equiv
      } where open Category C
    
    F₁ : ∀ {X Y} → Functor X Y → GraphMorphism (F₀ X) (F₀ Y)
    F₁ G = record
      { F₀        = G₀
      ; F₁        = G₁
      ; F-resp-≈  = G-resp-≡
      }
      where 
        open Functor G
          renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    
    .F-resp-≡ : ∀ {A B} {G H : Functor A B}
      → G ≡F H
      → F₁ G ≈ F₁ H
    F-resp-≡ {A}{B}{G}{H} G≡H {X}{Y} f = convert-~ (G≡H f)
      where
        open Heterogeneous (F₀ B)
          renaming (_~_ to _~₂_)
        open Categories.Category.Heterogeneous B
          renaming (_∼_ to _~₁_)
        
        convert-~ : ∀ {a b c d}{x : B [ a , b ]}{y : B [ c , d ]} → x ~₁ y → x ~₂ y
        convert-~ (≡⇒∼ foo) = ≈⇒~ foo
