{-# OPTIONS --universe-polymorphism #-}
module Categories.Limit where

open import Level

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.Cones
open import Categories.Object.Terminal as T using (Terminal; module Terminal)
import Categories.Morphisms as Mor
open import Categories.Cone using (module Cone)

module LimitsOf {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

  private module L = Terminal (Cones F)

  open Category C
  open Category J using () renaming (Obj to Dot)
  open Functor F
  open Mor C using (_≅_)
  open Mor (Cones F) using () renaming (_≅_ to _⇿_)
  open Category (Cones F) using () renaming (Obj to Cone; _≡_ to _≜_; _∘_ to _▵_; _⇒_ to _⇾_)

  -- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
  record Limit : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      terminal : Terminal (Cones F)

    private module terminal = Terminal (Cones F) terminal

    vertex : Obj
    vertex = Cone.N terminal.⊤

    proj : ∀ j → vertex ⇒ F₀ j
    proj = Cone.ψ terminal.⊤

    proj-cone : Cone
    proj-cone = terminal.⊤

    rep-cone : (K : Cone) → (K ⇾ proj-cone)
    rep-cone K = terminal.! {K}

    unrep-cone : ∀ {K : Cone} → (K ⇾ proj-cone) → Cone
    unrep-cone k = record
      { N = domain f
      ; ψ = λ j → proj j ∘ f
      ; commute = λ l → {!!} }
      where
      open ConeMorphism k using (f)
      open Cone proj-cone

      domain : ∀ {X Y} → X ⇒ Y → Obj
      domain {X} _ = X

    rep : (K : Cone) → (Cone.N K ⇒ vertex)
    rep K = ConeMorphism.f (terminal.! {K})

    .commute-cone : ∀ {K : Cone} → unrep-cone (rep-cone K) ≣ K
    commute-cone {K} = {!!}

  open Limit

  -- Properties
  -- 
  -- These are a little different from the raw ones for Terminal since they
  -- deal with isomorphisms in C instead of in Cones F.

  -- First, a lemma:

  isos-lift-to-cones : ∀ (c₁ c₂ : Cone) → _
  isos-lift-to-cones c₁ c₂ = {!!}

  up-to-iso : ∀ (c₁ c₂ : Cone) → _
  up-to-iso = {!!}