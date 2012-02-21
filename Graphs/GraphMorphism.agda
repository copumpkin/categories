{-# OPTIONS --universe-polymorphism #-}
module Graphs.GraphMorphism where

open import Data.Product
open import Level
open import Relation.Binary
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.HeterogeneousEquality as H
  using (_≅_)
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Support.PropositionalEquality

open import Graphs.Graph

record GraphMorphism {o₁ a₁ o₂ a₂}
    (A : Graph o₁ a₁) (B : Graph o₂ a₂) : Set (o₁ ⊔ o₂ ⊔ a₁ ⊔ a₂) where
  module A = Graph A
  module B = Graph B
  field
    F₀        : A.Obj → B.Obj
    F₁        : ∀ {X Y} → A [ X ↝ Y ] → B [ F₀ X ↝ F₀ Y ]

  .F-resp-≈ : ∀ {X Y}{f g : A [ X ↝ Y ]} → f ≣ g → F₁ f ≣ F₁ g
  F-resp-≈ = ≣-cong F₁

infixr 9 _∘_
infix  4 _≈_

id : ∀{o a}{A : Graph o a} → GraphMorphism A A
id = record
  { F₀        = λ A → A
  ; F₁        = λ f → f
  }

_∘_ : ∀ {o₀ a₀ o₁ a₁ o₂ a₂}
        {A : Graph o₀ a₀} {B : Graph o₁ a₁} {C : Graph o₂ a₂}
    → GraphMorphism B C → GraphMorphism A B → GraphMorphism A C
G ∘ F = record
  { F₀ = λ A → G₀ (F₀ A)
  ; F₁ = λ f → G₁ (F₁ f)
  } where
    open GraphMorphism F
    open GraphMorphism G renaming (F₀ to G₀; F₁ to G₁; F-resp-≈ to G-resp-≈)

_≈₀_ : ∀ {o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → (F G : GraphMorphism A B)
  → Set (o₁ ⊔ o₂)
_≈₀_ {A = A}{B} F G
  = ∀ X → F₀ X ≣ G₀ X
  where
    open GraphMorphism F using (F₀)
    open GraphMorphism G renaming (F₀ to G₀)

isEquivalence₀ : ∀{o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → IsEquivalence (_≈₀_ {A = A}{B}) 
isEquivalence₀ {A = A}{B} = record
  { refl  = λ     x → ≣-refl
  ; sym   = λ p   x → ≣-sym   (p x)
  ; trans = λ p q x → ≣-trans (p x) (q x)
  }

_≈₁_ : ∀ {o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → (F G : GraphMorphism A B)
  → Set (o₁ ⊔ a₁ ⊔ a₂)
_≈₁_ {A = A}{B} F G
  = ∀ {X Y} (f : A [ X ↝ Y ]) → B [ F₁ f ~ G₁ f ]
  where
    open GraphMorphism F using (F₁)
    open GraphMorphism G renaming (F₁ to G₁)

isEquivalence₁ : ∀{o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → IsEquivalence (_≈₁_ {A = A}{B}) 
isEquivalence₁ {A = A}{B} = record
  { refl  = λ     f → refl
  ; sym   = λ p   f → sym   (p f)
  ; trans = λ p q f → trans (p f) (q f)
  } where open Heterogeneous B

_≈_ : ∀ {o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → (F G : GraphMorphism A B)
  → Set (o₁ ⊔ o₂ ⊔ a₁ ⊔ a₂)
_≈_ = _≈₀_ -×- _≈₁_

isEquivalence : ∀{o₁ a₁ o₂ a₂} {A : Graph o₁ a₁} {B : Graph o₂ a₂}
  → IsEquivalence (_≈_ {A = A}{B})
isEquivalence {A = A}{B} = record
  { refl  = λ {x}       → refl₀  {x} , λ f → refl₁  {x} f
  ; sym   = λ {x}{y}    → map (sym₀   {x}{y})    (sym₁   {x}{y})
  ; trans = λ {x}{y}{z} → zip (trans₀ {x}{y}{z}) (trans₁ {x}{y}{z})
  } 
  where
    open IsEquivalence isEquivalence₀
      renaming (refl to refl₀; sym to sym₀; trans to trans₀)
    open IsEquivalence isEquivalence₁
      renaming (refl to refl₁; sym to sym₁; trans to trans₁)

.∘-resp-≈  : ∀ {o₀ a₀ o₁ a₁ o₂ a₂}
               {A : Graph o₀ a₀} {B : Graph o₁ a₁} {C : Graph o₂ a₂}
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
  helper₂ (≈⇒~ f≈h) (≈⇒~ g≈i) = ≈⇒~ (≣-trans (GraphMorphism.F-resp-≈ F f≈h) g≈i)

promote : ∀ {o₀ a₀ o₁ a₁} {A : Graph o₀ a₀} {B : Graph o₁ a₁}
          → (F G : GraphMorphism A B) → F ≈ G → F ≣ G
promote {A = A} {B} F G (F≈₀G , F≈₁G) = lemma (≣-ext F≈₀G) (wiggly (≣-ext F≈₀G) F≈₁G)
  where
  module F = GraphMorphism F
  module A = Graph A

  wiggly : ∀ {H₀} {H₁ : ∀ {X Y} → A [ X ↝ Y ] → B [ H₀ X ↝ H₀ Y ]} → (F.F₀ ≣ H₀) → (∀ {X Y} (f : A [ X ↝ Y ]) → B [ F.F₁ f ~ H₁ f ]) → (λ {X Y} → F.F₁ {X} {Y}) ≅ (λ {X Y} → H₁ {X} {Y})
  wiggly ≣-refl F₁∼H₁ = H.≡-to-≅ (≣-cong (λ h → λ {A B} → h A B) (≣-ext (λ X → ≣-ext (λ Y → ≣-ext (λ f → Heterogeneous.~⇒≈ B (F₁∼H₁ f))))))

  lemma : ∀ {G₀} {G₁ : ∀ {X Y : A.Obj} → _} (eq₀ : F.F₀ ≣ G₀) → (λ {X Y} → F.F₁ {X} {Y}) ≅ (λ {X Y} → G₁ {X} {Y}) → F ≣ record { F₀ = G₀ ; F₁ = (λ {X Y} → G₁ {X} {Y}) }
  lemma ≣-refl H.refl = ≣-refl
