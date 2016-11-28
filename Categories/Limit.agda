{-# OPTIONS --universe-polymorphism #-}
module Categories.Limit where

open import Level
open import Data.Product using (Σ; _,_; Σ-syntax; uncurry; proj₂)

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.Cones
open import Categories.Object.Terminal as T using (Terminal; module Terminal)
import Categories.Morphisms as Mor
open import Categories.Cone using (module Cone; module ConeOver)

module LimitsOf {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

  private module L = Terminal

  open Category C
  open Category J using () renaming (Obj to Dot)
  open Functor F
  open Mor C using (_≅_; _≡ⁱ_)
  open Mor (Cones F) using () renaming (_≅_ to _⇿_; _≡ⁱ_ to _≜ⁱ_)
  open Category (Cones F) using () renaming (Obj to Cone; _≡_ to _≜₁_; _∘_ to _▵_; _⇒_ to _⇾_; id to id▵)
  open ConeOver F using (_≜_; ≜-refl; ≜-sym; ≜-trans; heterogenize; homogenize; ConeUnder; tether; untether; _≜′_) renaming (module _≜_ to ≜; module _≜′_ to ≜′)
  open Heterogeneous C

  -- Isomorphic to an terminal object, but worth keeping distinct in case we change its definition
  record Limit : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      terminal : Terminal (Cones F)

    private module terminal = Terminal terminal
    module Fl = Float F

    {-
    vertex : Obj
    vertex = Cone.N terminal.⊤

    proj : ∀ j → vertex ⇒ F₀ j
    proj = Cone.ψ terminal.⊤

    proj-cone : Cone
    proj-cone = terminal.⊤
    -}

    open terminal public using () renaming (⊤ to proj-cone)
    open Cone proj-cone public using () renaming (N to vertex; ψ to proj)

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
      ≡⇒∼ʳ (≜.N-≣ K₁≜K₂) (rep-cone-cong K₁≜K₂)

    .rep-cone∘ : ∀ {K K′} {q : K′ ⇾ K} → Cones F [ Cones F [ rep-cone K ∘ q ] ≡ rep-cone K′ ]
    rep-cone∘ {K} {q = q} = Equiv.sym (terminal.!-unique (rep-cone K ▵ q))

    .rep∘ : ∀ {K K′} {q : K′ ⇾ K} → rep K ∘ ConeMorphism.f q ≡ rep K′
    rep∘ {K} {K′} {q} = rep-cone∘ {K} {K′} {q}

    .rep-cone-self-id : rep-cone proj-cone ≜₁ id▵
    rep-cone-self-id = terminal.!-unique id▵

    .rep-self-id : rep proj-cone ≡ id
    rep-self-id = terminal.!-unique id▵

  open Limit

  -- Properties
  -- 
  -- These are a little different from the raw ones for Terminal since they
  -- deal with isomorphisms in C instead of in Cones F.

  -- First, a lemma:

  open import Categories.Square

  -- do these lemmas belong in Cones?

  isos-lift-to-cones : ∀ (κ : Cone) {v : Obj} → Cone.N κ ≅ v → Σ[ κ′ ∈ Cone ] κ ⇿ κ′
  isos-lift-to-cones κ {v} κ≅v =
      record
      { N = v
      ; ψ = λ X → (Cone.ψ κ X) ∘ g
      ; commute = λ f' → pullˡ (Cone.commute κ f')
      } 
    , record
      { f = record { f = f; commute = Equiv.sym (cancelRight isoˡ) }
      ; g = record { f = g; commute = Equiv.refl }
      ; iso = record { isoˡ = isoˡ; isoʳ = isoʳ }
      }
    where
    open Mor._≅_ κ≅v
    open GlueSquares C

  isos-lower-from-cones : ∀ {κ₁ κ₂ : Cone} → κ₁ ⇿ κ₂ → Cone.N κ₁ ≅ Cone.N κ₂
  isos-lower-from-cones κ₁⇿κ₂ = record
    { f = ConeMorphism.f f
    ; g = ConeMorphism.f g
    ; iso = record { isoˡ = isoˡ; isoʳ = isoʳ }
    }
    where
    open Mor._≅_ κ₁⇿κ₂

  ≜ⁱ⇒≡ⁱ : ∀ {κ₁ κ₂} {i₁ i₂ : κ₁ ⇿ κ₂} → i₁ ≜ⁱ i₂
        → isos-lower-from-cones i₁ ≡ⁱ isos-lower-from-cones i₂
  ≜ⁱ⇒≡ⁱ pf = record { f-≡ = f-≡; g-≡ = g-≡ }
    where open Mor._≡ⁱ_ pf

  up-to-iso-cone : (L₁ L₂ : Limit) → proj-cone L₁ ⇿ proj-cone L₂
  up-to-iso-cone L₁ L₂ = T.up-to-iso (Cones F) (terminal L₁) (terminal L₂)

  up-to-iso : (L₁ L₂ : Limit) → vertex L₁ ≅ vertex L₂
  up-to-iso L₁ L₂ = isos-lower-from-cones (up-to-iso-cone L₁ L₂)

  transport-by-iso-cone : (L : Limit) {κ : Cone} → proj-cone L ⇿ κ → Limit
  transport-by-iso-cone L L⇿κ = record
    { terminal = T.transport-by-iso (Cones F) (terminal L) L⇿κ
    }

  transport-by-iso : (L : Limit) {v : Obj} → vertex L ≅ v → Limit
  transport-by-iso L L≅v = transport-by-iso-cone L (proj₂ p)
    where p = isos-lift-to-cones (proj-cone L) L≅v

  .up-to-iso-cone-unique : ∀ L L′ → (i : proj-cone L ⇿ proj-cone L′) → up-to-iso-cone L L′ ≜ⁱ i
  up-to-iso-cone-unique L L′ i = T.up-to-iso-unique (Cones F) (terminal L) (terminal L′) i

  -- XXX probably not true -- what is?  only the above?
  -- .up-to-iso-unique : ∀ L L′ → (i : vertex L ≅ vertex L′) → up-to-iso L L′ ≡ⁱ i
  -- up-to-iso-unique L L′ i = ≜ⁱ⇒≡ⁱ {!up-to-iso-unique-cone L L′ !}

  .up-to-iso-cone-invˡ : ∀ {L κ} {i : proj-cone L ⇿ κ} → up-to-iso-cone L (transport-by-iso-cone L i) ≜ⁱ i
  up-to-iso-cone-invˡ {L} {i = i} = up-to-iso-cone-unique L (transport-by-iso-cone L i) i

  .up-to-iso-invˡ : ∀ {L X} {i : vertex L ≅ X} → up-to-iso L (transport-by-iso L i) ≡ⁱ i
  up-to-iso-invˡ {L₁} {i = i} = ≜ⁱ⇒≡ⁱ (up-to-iso-cone-invˡ {L₁} {i = proj₂ (isos-lift-to-cones (proj-cone L₁) i)})

  up-to-iso-cone-invʳ : ∀ {L L′} → proj-cone (transport-by-iso-cone L (up-to-iso-cone L L′)) ≜ proj-cone L′
  up-to-iso-cone-invʳ {L} {L′} = ≜-refl

  up-to-iso-invʳ : ∀ {L L′} → vertex (transport-by-iso L (up-to-iso L L′)) ≣ vertex L′
  up-to-iso-invʳ {t} {t′} = ≣-refl
