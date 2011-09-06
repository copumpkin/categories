{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda.Cocomplete where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)
open import Data.Product using (Σ; _,_)
open import Function.Equality using (module Π)
-- import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Support.Equivalence using (setoid-i→r; setoid-r→i; I→R-Wrapper; module I→R-Wrapper) renaming (Setoid to ISetoid; module Setoid to ISetoid)
open import Categories.Support.PropositionalEquality
import Categories.Support.ZigZag as ZigZag

open import Categories.Category
open import Categories.Functor
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone

SetoidsCocomplete : ∀ {o ℓ e o′} → Cocomplete o ℓ e (Setoids (o′ ⊔ suc (o ⊔ ℓ ⊔ e)) (o′ ⊔ suc (o ⊔ ℓ ⊔ e)))
SetoidsCocomplete {o} {ℓ} {e} {o′} = record { colimit = colimit }
  where
  ℓ′ = o′ ⊔ suc (o ⊔ ℓ ⊔ e)
  C = Setoids ℓ′ ℓ′
  colimit : ∀ {J : Category o ℓ e} (F : Functor J C) → Colimit F
  colimit {J} F = record { initial = my-initial-cocone }
    where
    D = Cocones F
    module J = Category J
    open Functor F
    open Setoid
    open Π
    open I→R-Wrapper
    vertex-carrier = Σ[ x ∶ J.Obj ] Carrier (F₀ x)

    -- this allows us to use the functor laws to prove that identities in J
    -- map to identities in Setoids
    dot-setoid : (j : J.Obj) → Setoid ℓ′ ℓ′
    dot-setoid j = setoid-i→r (setoid-r→i (F₀ j))
    module DotSetoid (j : J.Obj) = Setoid (dot-setoid j)
    open DotSetoid using () renaming (_≈_ to _[_≈_])

    -- _↝_ means that an arrow in the diagram directly constrains the two
    -- objects of vertex-carrier to be equal.  completing this to an
    -- equivalence relation gives us the setoid we need
    _↝_ : (i j : vertex-carrier) → Set ℓ′
    (j₁ , x₁) ↝ (j₂ , x₂) = Σ[ f ∶ J [ j₁ , j₂ ] ] (j₂ [ (F₁ f ⟨$⟩ x₁) ≈ x₂ ])

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
      ↝-refl {j , x} = J.id , squash identity

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
      ↝-trans {k = k₁ , _} (f , squash fi≈j) (g , gj≈k) =
        J [ g ∘ f ] , DotSetoid.trans k₁ (squash (trans (F₀ k₁) homomorphism (cong (F₁ g) fi≈j))) gj≈k
 
    vertex = ZigZag.setoid ↝-preorder

    my-initial-cocone-object = record
      { N = vertex
      ; ψ = λ X → record
        { _⟨$⟩_ = _,_ X
        ; cong = λ pf → ZigZag.disorient (ZigZag.slish (J.id , squash (trans (F₀ X) identity pf)))
      -- cong would be easier if i'd used the proper dotwise equality for
      -- ↝-preorder above ... since this is basically the proof ↝ respects it
      }
      ; commute = λ {X Y} f {x} → ZigZag.disorient (ZigZag.slish (f , (squash (refl (F₀ Y)))))
      }

    my-! : {A : Cocone F} → CoconeMorphism {F = F} my-initial-cocone-object A
    my-! {A} = record
      { f = record
        { _⟨$⟩_ = my-f
        ; cong = ZigZag.minimal ↝-preorder A.N my-f {!!}
        }
      ; commute = {!!}
      }
      where
      module A = Cocone A
      my-f : vertex-carrier → Carrier A.N
      my-f (X , x) = A.ψ X ⟨$⟩ x

      .my-precong : _↝_ =[ my-f ]⇒ (_≈_ A.N)
      my-precong {X , x} {Y , y} (f , squash fx≈y) = ?

    my-initial-cocone = record
      { ⊥ = my-initial-cocone-object
      ; ! = my-!
      ; !-unique = {!!}
      }
