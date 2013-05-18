{-# OPTIONS --universe-polymorphism #-}
module Categories.Agda.ISetoids.Cocomplete.Helpers where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)
open import Data.Product using (Σ; _,_; Σ-syntax)
-- import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Support.Equivalence using (module I→R-Wrapper; setoid-i→r; squash) renaming (Setoid to ISetoid; module Setoid to ISetoid)
open import Categories.Support.SetoidFunctions using (module _⟶_)
open import Categories.Support.PropositionalEquality
import Categories.Support.ZigZag as ZigZag

open import Categories.Category
open import Categories.Functor
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone

open I→R-Wrapper

ding : Level → Level
ding ℓ = ℓ

module ColimitCocone {o ℓ e c ℓ′} {J : Category o ℓ e} (F : Functor J (ISetoids (c ⊔ ding (o ⊔ ℓ ⊔ e)) (c ⊔ ℓ′ ⊔ ding (o ⊔ ℓ ⊔ e)))) where
  c′ = c ⊔ ding (o ⊔ ℓ ⊔ e)
  ℓ″ = c ⊔ ℓ′ ⊔ ding (o ⊔ ℓ ⊔ e)
  C = ISetoids c′ ℓ″
  D = Cocones F
  module J = Category J
  open Functor F
  open ISetoid
  open _⟶_

  vertex-carrier = Σ[ x ∈ J.Obj ] Carrier (F₀ x)

  -- this lets us build a preorder out of an irrelevant setoid, since there
  -- are no irrelevant preorders
  dot-setoid : (j : J.Obj) → Setoid c′ ℓ″
  dot-setoid j = setoid-i→r (F₀ j)
  module DotSetoid (j : J.Obj) = Setoid (dot-setoid j)
  open DotSetoid using () renaming (_≈_ to _[_≈_])

  -- _↝_ means that an arrow in the diagram directly constrains the two
  -- objects of vertex-carrier to be equal.  completing this to an
  -- equivalence relation gives us the setoid we need
  _↝_ : (x y : vertex-carrier) → Set ℓ″
  (X , x) ↝ (Y , y) = Σ[ f ∈ J [ X , Y ] ] (Y [ (F₁ f ⟨$⟩ x) ≈ y ])

  ↝-preorder : Preorder c′ c′ ℓ″
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
    ↝-refl {X , x} = J.id , squash (identity (refl (F₀ X)))

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
    ↝-trans {X , _} {k = Z , _} (f , squash fx≈y) (g , gy≈z) =
      J [ g ∘ f ] , DotSetoid.trans Z (squash (trans (F₀ Z) (homomorphism (refl (F₀ X))) (cong (F₁ g) fx≈y))) gy≈z
 
  vertex = ZigZag.isetoid ↝-preorder

  ⊥ : Cocone F
  ⊥ = record
    { N = vertex
    ; ψ = λ X → record
      { _⟨$⟩_ = _,_ X
      ; cong = λ pf → ZigZag.disorient (ZigZag.slish (J.id , squash (identity pf)))
    -- cong would be easier if i'd used the proper dotwise equality for
    -- ↝-preorder above ... since this is basically the proof ↝ respects it
    }
    ; commute = λ {X Y} f {x : _} {y : _} (x≈y : _) → ZigZag.disorient (ZigZag.slish (f , (squash (cong (F₁ f) x≈y))))
    }

  ! : {A : Cocone F} → CoconeMorphism {F = F} ⊥ A
  ! {A} = record
    { f = record
      { _⟨$⟩_ = my-f
      ; cong = ZigZag.iminimal ↝-preorder A.N my-f my-precong
      }
    ; commute = λ {X x y} x≈y → cong (A.ψ X) x≈y
    }
    where
    module A = Cocone A
    my-f : vertex-carrier → Carrier A.N
    my-f (X , x) = A.ψ X ⟨$⟩ x

    .my-precong : _↝_ =[ my-f ]⇒ (_≈_ A.N)
    my-precong {X , x} {Y , y} (f , squash fx≈y) = trans A.N (A.commute f (refl (F₀ X))) (cong (A.ψ Y) (irr fx≈y))
