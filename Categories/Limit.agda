{-# OPTIONS --universe-polymorphism #-}
module Categories.Limit where

open import Level

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.Cones
open import Categories.Object.Terminal as T using (Terminal; module Terminal)
import Categories.Morphisms as Mor
open import Categories.Cone using (module Cone; module ConeOver)

module LimitsOf {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

  private module L = Terminal (Cones F)

  open Category C
  open Category J using () renaming (Obj to Dot)
  open Functor F
  open Mor C using (_≅_)
  open Mor (Cones F) using () renaming (_≅_ to _⇿_)
  open Category (Cones F) using () renaming (Obj to Cone; _≡_ to _≜₁_; _∘_ to _▵_; _⇒_ to _⇾_)
  open ConeOver F using (_≜_; ≜-sym; ≜-trans; heterogenize; homogenize; ConeUnder; tether; untether; _≜′_)
  open Heterogeneous C

  -- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
  record Limit : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      terminal : Terminal (Cones F)

    private module terminal = Terminal (Cones F) terminal
    module Fl = Float F

    {-
    vertex : Obj
    vertex = Cone.N terminal.⊤

    proj : ∀ j → vertex ⇒ F₀ j
    proj = Cone.ψ terminal.⊤

    proj-cone : Cone
    proj-cone = terminal.⊤
    -}

    open terminal using () renaming (⊤ to proj-cone)
    open Cone proj-cone using () renaming (N to vertex; ψ to proj)

    rep-cone : (K : Cone) → (K ⇾ proj-cone)
    rep-cone K = terminal.! {K}

    rep : (K : Cone) → (Cone.N K ⇒ vertex)
    rep K = ConeMorphism.f (terminal.! {K})

    unrep : ∀ {X} → (X ⇒ vertex) → Cone
    unrep f = record
      { N = domain f
      ; ψ = λ j → proj j ∘ f
      ; commute = λ l → Equiv.trans (Equiv.sym assoc) (∘-resp-≡ˡ (commute l))
      }
      where
      open Cone proj-cone

    conify : ∀ {X} (f : X ⇒ vertex) → (unrep f ⇾ proj-cone)
    conify f = record { f = f; commute = Equiv.refl }

    unrep-cone : ∀ {K : Cone} → (K ⇾ proj-cone) → Cone
    unrep-cone κ = unrep (ConeMorphism.f κ)

    commute-cone : ∀ {K : Cone} → unrep-cone (rep-cone K) ≜ K
    commute-cone {K} = record
      { N-≣ = ≣-refl
      ; ψ-≡ = λ j → ≡⇒∼ (Equiv.sym (ConeMorphism.commute (rep-cone K)))
      }

    .commute : ∀ K j → proj j ∘ rep K ≡ Cone.ψ K j
    commute K = λ j → Equiv.sym (ConeMorphism.commute (rep-cone K))

    private
      domain▵ : ∀ {X Y} → X ⇾ Y → Cone
      domain▵ {X} _ = X

    .universal-cone : ∀ {K : Cone} {i : K ⇾ proj-cone} → unrep-cone i ≜ K → Cones F [ rep-cone K ≡ i ]
    universal-cone {K} {i} pf = terminal.!-unique i

    .universal : ∀ {K : Cone} {i : Cone.N K ⇒ vertex} → unrep i ≜ K → rep K ≡ i
    universal {K} {i} pf = terminal.!-unique (Fl.floatʳ (heterogenize (homogenize pf ≣-refl)) (conify i))
    -- complicated, isn't it?  but it's necessary in order to make the float
    --   compute enough for the !-unique to typecheck.  by replacing the
    --   N-≣ in pf with ≣-refl we can make it happen!

    g-η-cone₀ : ∀ {K} {κ : K ⇾ proj-cone} → K ≜ unrep-cone κ
    g-η-cone₀ {K} {κ} = record { N-≣ = ≣-refl; ψ-≡ = λ j → ≡⇒∼ (ConeMorphism.commute κ) }

    .g-η-cone : ∀ {K} {κ : K ⇾ proj-cone} → rep-cone (unrep-cone κ) ≜₁ Fl.floatʳ (g-η-cone₀ {κ = κ}) κ
    g-η-cone {κ = κ} = terminal.!-unique (Fl.floatʳ (g-η-cone₀ {κ = κ}) κ)

    .g-η : ∀ {X} {f : X ⇒ vertex} → rep (unrep f) ≡ f
    g-η {f = f} = terminal.!-unique (conify f)

    .η-cone : Cones F [ rep-cone proj-cone ≡ Category.id (Cones F) ]
    η-cone = terminal.⊤-id (rep-cone proj-cone)

    .η : rep proj-cone ≡ id
    η = η-cone

    .rep-cone-cong : ∀ {K₁ K₂} (K₁≜K₂ : K₁ ≜ K₂) → Cones F [ Fl.floatʳ K₁≜K₂ (rep-cone K₁) ≡ rep-cone K₂ ]
    rep-cone-cong {K₁} {K₂} K₁≜K₂ = 
      Equiv.sym (terminal.!-unique (Fl.floatʳ K₁≜K₂ (rep-cone K₁)))

    .rep-cong′ : ∀ {N} {K₁ K₂ : ConeUnder N} → K₁ ≜′ K₂ → rep (untether K₁) ≡ rep (untether K₂)
    rep-cong′ {N} {K₁} {K₂} K₁≜′K₂ = 
      Equiv.sym (terminal.!-unique (Fl.floatʳ (heterogenize K₁≜′K₂) (rep-cone (untether K₁))))

    rep-cong : ∀ {K₁ K₂} → K₁ ≜ K₂ → rep K₁ ∼ rep K₂
    rep-cong K₁≜K₂ = 
      {!≡⇒∼!}

    .rep-cone∘ : ∀ {K K′} {q : K′ ⇾ K} → Cones F [ Cones F [ rep-cone K ∘ q ] ≡ rep-cone K′ ]
    rep-cone∘ = {!sym (universal (pullˡ commute₁) (pullˡ commute₂))!}

    .rep∘ : ∀ {K K′} {q : K′ ⇾ K} → rep K ∘ ConeMorphism.f q ≡ rep K′
    rep∘ = {!sym (universal (pullˡ commute₁) (pullˡ commute₂))!}

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