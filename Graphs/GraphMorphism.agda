{-# OPTIONS --universe-polymorphism #-}
module Graphs.GraphMorphism where

open import Data.Product
open import Level
open import Relation.Binary
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
  using ()
  renaming
    (_≡_ to _≣_
    ; refl  to ≣-refl
    ; sym   to ≣-sym
    ; trans to ≣-trans
    ; cong  to ≣-cong
    )

open import Graphs.Graph

record GraphMorphism {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
    (A : Graph o₁ ℓ₁ e₁) (B : Graph o₂ ℓ₂ e₂) : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e₁ ⊔ e₂) where
  module A = Graph A
  module B = Graph B
  field
    F₀        : A.Obj → B.Obj
    F₁        : ∀ {X Y} → A [ X ↝ Y ] → B [ F₀ X ↝ F₀ Y ]
    .F-resp-≈ : ∀ {X Y}{f g : A [ X ↝ Y ]} → A [ f ≈ g ] → B [ F₁ f ≈ F₁ g ]

infixr 9 _∘_
infix  4 _≈_

id : ∀{o ℓ e}{A : Graph o ℓ e} → GraphMorphism A A
id = record
  { F₀        = λ A → A
  ; F₁        = λ f → f
  ; F-resp-≈  = λ f≈g → f≈g
  }

_∘_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
        {A : Graph o₀ ℓ₀ e₀} {B : Graph o₁ ℓ₁ e₁} {C : Graph o₂ ℓ₂ e₂}
    → GraphMorphism B C → GraphMorphism A B → GraphMorphism A C
G ∘ F = record
  { F₀ = λ A → G₀ (F₀ A)
  ; F₁ = λ f → G₁ (F₁ f)
  ; F-resp-≈ = λ f≈g → G-resp-≈ (F-resp-≈ f≈g)
  } where
    open GraphMorphism F
    open GraphMorphism G renaming (F₀ to G₀; F₁ to G₁; F-resp-≈ to G-resp-≈)

_≈_ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {A : Graph o₁ ℓ₁ e₁} {B : Graph o₂ ℓ₂ e₂}
  → (F G : GraphMorphism A B)
  → Set _
_≈_ {A = A}{B} F G
  = (∀ X → F₀ X ≣ G₀ X)
  × (∀ {X Y} (f : A [ X ↝ Y ]) → B [ F₁ f ~ G₁ f ])
  where
    open GraphMorphism F using (F₀; F₁)
    open GraphMorphism G renaming (F₀ to G₀; F₁ to G₁)

isEquivalence : ∀{o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {A : Graph o₁ ℓ₁ e₁} {B : Graph o₂ ℓ₂ e₂}
  → IsEquivalence (_≈_ {o₁}{ℓ₁}{e₁}{o₂}{ℓ₂}{e₂}{A}{B})
isEquivalence {A = A}{B} = record
  { refl  = (λ x → ≣-refl)
          , (λ f → refl)
  ; sym   = λ p   → (λ x → ≣-sym (proj₁ p x))
                  , (λ f → sym   (proj₂ p f))
  ; trans = λ p q → (λ x → ≣-trans (proj₁ p x) (proj₁ q x))
                  , (λ f → trans   (proj₂ p f) (proj₂ q f))
  } where open Heterogeneous B

.∘-resp-≈  : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
               {A : Graph o₀ ℓ₀ e₀} {B : Graph o₁ ℓ₁ e₁} {C : Graph o₂ ℓ₂ e₂}
               {F H : GraphMorphism B C} {G I : GraphMorphism A B}
           → F ≈ H → G ≈ I → F ∘ G ≈ H ∘ I
∘-resp-≈ {B = B} {C} {F}{H}{G}{I} F≈H G≈I
  = (λ x → helper₁ (proj₁ G≈I x) (proj₁ F≈H (GraphMorphism.F₀ I x)))
  , (λ q → helper₂ (proj₂ G≈I q) (proj₂ F≈H (GraphMorphism.F₁ I q)))
  where 
  open Heterogeneous C
  module C = Graph C
  helper₁ : ∀ {x}
    → GraphMorphism.F₀ G x ≣ GraphMorphism.F₀ I x 
    → GraphMorphism.F₀ F (GraphMorphism.F₀ I x) ≣ GraphMorphism.F₀ H (GraphMorphism.F₀ I x)
    → GraphMorphism.F₀ F (GraphMorphism.F₀ G x) ≣ GraphMorphism.F₀ H (GraphMorphism.F₀ I x)
  helper₁ g≣i f≣h = ≣-trans (≣-cong (GraphMorphism.F₀ F) g≣i) f≣h

  helper₂ : ∀ {a b c d} {z w} {f : B [ a ↝ b ]} {h : B [ c ↝ d ]} {i : C [ z ↝ w ]} 
         → B [ f ~ h ] → C [ GraphMorphism.F₁ F h ~ i ] → C [ GraphMorphism.F₁ F f ~ i ]
  helper₂ (≈⇒~ f≈h) (≈⇒~ g≈i) = ≈⇒~ (C.Equiv.trans (GraphMorphism.F-resp-≈ F f≈h) g≈i)
