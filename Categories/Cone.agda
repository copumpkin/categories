{-# OPTIONS --universe-polymorphism #-}
module Categories.Cone where

open import Level
open import Relation.Binary using (IsEquivalence; Setoid; module Setoid)

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor hiding (_≡_; _∘_)

module ConeOver {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where
  module J = Category J
  open Category C
  open Functor F
  record Cone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    field
      N : Obj
      ψ : ∀ X → (N ⇒ F₀ X)
      .commute : ∀ {X Y} (f : J [ X , Y ]) → F₁ f ∘ ψ X ≡ ψ Y

  Cone′ = Cone

  record _≜_ (X Y : Cone) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    module X = Cone X
    module Y = Cone Y
    field
      N-≣ : X.N ≣ Y.N
      ψ-≡ : ∀ j → C [ X.ψ j ∼ Y.ψ j ]

  ≜-is-equivalence : IsEquivalence _≜_
  ≜-is-equivalence = record
    { refl = record { N-≣ = ≣-refl; ψ-≡ = λ j → refl }
    ; sym = λ X≜Y → let module X≜Y = _≜_ X≜Y in record
      { N-≣ = ≣-sym X≜Y.N-≣
      ; ψ-≡ = λ j → sym (X≜Y.ψ-≡ j)
      }
    ; trans = λ X≜Y Y≜Z →
      let module X≜Y = _≜_ X≜Y in
      let module Y≜Z = _≜_ Y≜Z in
      record
        { N-≣ = ≣-trans X≜Y.N-≣ Y≜Z.N-≣
        ; ψ-≡ = λ j → trans (X≜Y.ψ-≡ j) (Y≜Z.ψ-≡ j)
        }
    }
    where open Heterogeneous C

  cone-setoid : Setoid _ _
  cone-setoid = record
    { Carrier = Cone
    ; _≈_ = _≜_
    ; isEquivalence = ≜-is-equivalence
    }

  record ConeUnder (N : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    field
      ψ′ : ∀ X → (N ⇒ F₀ X)
      .commute : ∀ {X Y} (f : J [ X , Y ]) → F₁ f ∘ ψ′ X ≡ ψ′ Y

  ConeUnder′ = ConeUnder

  untether : ∀ {N} → ConeUnder N → Cone
  untether {N} K = record { N = N; ψ = ψ′; commute = commute }
    where open ConeUnder K

  -- this Henry Ford bit is a little weird but it turns out to be handy
  tether : ∀ {N} → (K : Cone) → (N ≣ Cone.N K) → ConeUnder N
  tether K ≣-refl = record { ψ′ = Cone.ψ K; commute = Cone.commute K }

  record _≜′_ {N} (X Y : ConeUnder N) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
    module X = ConeUnder X
    module Y = ConeUnder Y
    field
      .ψ′-≡ : ∀ j → C [ X.ψ′ j ≡ Y.ψ′ j ]

  ≜′-is-equivalence : (N : Obj) → IsEquivalence (_≜′_ {N})
  ≜′-is-equivalence N = record
    { refl = record { ψ′-≡ = λ j → Equiv.refl }
    ; sym = λ X≜′Y → let module X≜′Y = _≜′_ X≜′Y in record
      { ψ′-≡ = λ j → Equiv.sym (X≜′Y.ψ′-≡ j)
      }
    ; trans = λ X≜′Y Y≜′Z →
      let module X≜′Y = _≜′_ X≜′Y in
      let module Y≜′Z = _≜′_ Y≜′Z in
      record { ψ′-≡ = λ j → Equiv.trans (X≜′Y.ψ′-≡ j) (Y≜′Z.ψ′-≡ j) }
    }
    where open Heterogeneous C

  cone-under-setoid : (N : Obj) → Setoid _ _
  cone-under-setoid N = record
    { Carrier = ConeUnder N
    ; _≈_ = _≜′_
    ; isEquivalence = ≜′-is-equivalence N
    }

  private
    .lemma₁ : ∀ {N j} {f : N ⇒ F₀ j} K → C [ f ∼ Cone.ψ K j ] → (pf : N ≣ Cone.N K) → f ≡ ConeUnder.ψ′ (tether K pf) j
    lemma₁ K eq ≣-refl = ∼⇒≡ eq
      where open Heterogeneous C

  -- allow replacing the N-≣ because sometimes refl is available at the place
  --   of use.  in fact that's the main reason to even have ConeUnders.
  --   coincidentally, it makes this easier to write!
  homogenize : ∀ {K₁ K₂} → K₁ ≜ K₂ → (pf : Cone.N K₁ ≣ Cone.N K₂) → tether K₁ ≣-refl ≜′ tether K₂ pf
  homogenize {K₂ = K₂} K₁≜K₂ pf = record { ψ′-≡ = λ j → lemma₁ K₂ (ψ-≡ j) pf }
    where
    open _≜_ K₁≜K₂
    open Heterogeneous C

  heterogenize : ∀ {N} {K₁ K₂ : ConeUnder N} → K₁ ≜′ K₂ → untether K₁ ≜ untether K₂
  heterogenize {N} {K₁} {K₂} pf = record
    { N-≣ = ≣-refl
    ; ψ-≡ = λ j → Heterogeneous.≡⇒∼ (ψ′-≡ j)
    }
    where open _≜′_ pf

  open Setoid cone-setoid public renaming (refl to ≜-refl; sym to ≜-sym; trans to ≜-trans; reflexive to ≜-reflexive)
  module ≜′ {N : Obj} = Setoid (cone-under-setoid N)

open ConeOver public using (cone-setoid) renaming (_≜_ to _[_≜_]; Cone′ to Cone; _≜′_ to _[_≜′_]; ConeUnder′ to ConeUnder)

module Cone {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {F : Functor J C} (K : ConeOver.Cone F) = ConeOver.Cone K
