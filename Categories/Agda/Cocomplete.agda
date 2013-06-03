{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda.Cocomplete where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)
open import Data.Product using (Σ; _,_)
open import Function.Equality using (module Π)
-- import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Support.Irrelevance
open import Categories.Support.PropositionalEquality
open import Categories.Support.IProduct using (Σ′; _,_)
import Categories.Support.ZigZag as ZigZag
open import Categories.Support.Quotients

open import Categories.Category
open import Categories.Functor hiding (promote)
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone

SetsCocomplete : ∀ {o a o′} → Cocomplete o a (Sets (o′ ⊔ suc (o ⊔ a)))
SetsCocomplete {o} {a} {o′} = record { colimit = colimit }
  where
  ℓ′ = o′ ⊔ suc (o ⊔ a)
  C = Sets ℓ′

  colimit : ∀ {J : Category o a} (F : Functor J C) → Colimit F
  colimit {J} F = record { initial = my-initial-cocone }
    where
    D = Cocones F
    module J = Category J
    open Functor F
    open EasyCategory (Coconesᵉ F) using (promote)
    vertex-carrier = Σ J.Obj (λ x → F₀ x)

    -- _↝_ means that an arrow in the diagram directly constrains the two
    -- objects of vertex-carrier to be equal.  completing this to an
    -- equivalence relation gives us the setoid we need
    _↝_ : (i j : vertex-carrier) → Set ℓ′
    (j₁ , x₁) ↝ (j₂ , x₂) = Σ′[ f ∶ J [ j₁ , j₂ ] ] (F₁ f x₁ ≣ x₂)

    ↝-preorder : Preorder ℓ′ ℓ′ ℓ′
    ↝-preorder = record
      { Carrier = vertex-carrier
      ; _≈_ = _≣_
      ; _∼_ = _↝_
      ; isPreorder = record
        { isEquivalence = ≣-isEquivalence
        ; reflexive = ↝-reflexive
        ; trans = ↝-trans
        }
      }
      where
      ↝-refl : ∀ {i} → (i ↝ i)
      ↝-refl {j , x} = J.id , ≣-app identity-relevant x

      ↝-reflexive : ∀ {i j} → (i ≣ j) → (i ↝ j)
      ↝-reflexive ≣-refl = ↝-refl

      -- the nice proof.  pretty proof!
      {-
      ↝-trans : ∀ {i j k} → (i ↝ j) → (j ↝ k) → (i ↝ k)
      ↝-trans {_ , i} {_ , j} {k₁ , k} (f , squash fi≈j) (g , gj≈k) =
        J [ g ∘ f ] , (
          begin
            F₁ (J [ g ∘ f ]) ⟨$⟩ i
          ≈⟨ squash homomorphism ⟩
            F₁ g ⟨$⟩ (F₁ f ⟨$⟩ i)
          ≈⟨ squash (cong (F₁ g) fi≈j) ⟩
            F₁ g ⟨$⟩ j
          ≈⟨ gj≈k ⟩
            k
          ∎ )
        where
        open EqReasoning (dot-setoid k₁)
      -}

      -- the ugly proof that loads before the sun burns out.
      ↝-trans : ∀ {i j k} → (i ↝ j) → (j ↝ k) → (i ↝ k)
      ↝-trans {i = i₁ , i₂} (f , fi≈j) (g , gj≈k) =
        J [ g ∘ f ] , ≣-trans (≣-trans (≣-app homomorphism i₂) (≣-cong (F₁ g) fi≈j)) gj≈k
 
    module ZZ = ZigZag ↝-preorder

    vertex = Quotient vertex-carrier ZZ.Alternating ZZ.is-equivalence

    my-initial-cocone-object : Cocone F
    my-initial-cocone-object = record
      { N = vertex
      ; ψ = λ X x → ⌊ X , x ⌉
      ; commute = λ {X Y} f → ≣-ext λ x → qdiv (ZZ.disorient (ZZ.slish (f , ≣-refl)))
      }

    my-!-f : (A : Cocone F) → vertex-carrier → Cocone.N A
    my-!-f A (X , x) = A.ψ X x
      where module A = Cocone A

    .my-!-cong : (A : Cocone F) → ZZ.Alternating =[ my-!-f A ]⇒ _≣_
    my-!-cong A = ZZ.minimal (≣-setoid A.N) (my-!-f A) my-precong
      where
      module A = Cocone A

      .my-precong : _↝_ =[ my-!-f A ]⇒ _≣_
      my-precong {X , x} {Y , y} (f , fx≈y) = (≣-trans (≣-app (A.commute f) x) (≣-cong (A.ψ Y) (irr fx≈y)))

    my-! : {A : Cocone F} → CoconeMorphism {F = F} my-initial-cocone-object A
    my-! {A} = record
      { f = my-f′
      ; commute = λ {X} → ≣-ext λ x → qelim-compute′ (my-!-cong A)
      }
      where
      module A = Cocone A

      my-f′ : vertex → A.N
      my-f′ = qelim′ (my-!-f A) (my-!-cong A)

    .my-!-unique : (A : Cocone F)
                   (φ : CoconeMorphism my-initial-cocone-object A)
                   (x : vertex-carrier)
                 → CoconeMorphism.f (my-! {A}) ⌊ x ⌉ ≣ CoconeMorphism.f φ ⌊ x ⌉
    my-!-unique A φ (X , x) = ≣-trans
      (qelim-compute′ (my-!-cong A))
      (≣-sym (≣-app (CoconeMorphism.commute φ) x))

    my-initial-cocone : Initial (Cocones F)
    my-initial-cocone = record
      { ⊥ = my-initial-cocone-object
      ; ! = my-!
      ; !-unique = λ {A} φ → promote my-! φ (≣-ext (qequate′ (my-!-unique A φ)))
      }
