{-# OPTIONS --universe-polymorphism #-}
module Categories.2-Category where

open import Level
open import Data.Product using (curry; _,_)
open import Function using () renaming (_∘_ to _·_)

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Categories
open import Categories.Object.Terminal
open import Categories.Terminal
open import Categories.Functor using (Functor) renaming (_∘_ to _∘F_; _≡_ to _≡F_; id to idF)
open import Categories.Bifunctor using (Bifunctor; reduce-×)
open import Categories.Product using (assocʳ; πˡ; πʳ)

record 2-Category (o ℓ t e : Level) : Set (suc (o ⊔ ℓ ⊔ t ⊔ e)) where
  open Terminal (One {ℓ} {t} {e})

  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Category ℓ t e
    id : {A : Obj} → Functor ⊤ (A ⇒ A)
    —∘— : {A B C : Obj} → Bifunctor (B ⇒ C) (A ⇒ B) (A ⇒ C)
  _∘_ : {A B C : Obj} {L R : Category ℓ t e} → Functor L (B ⇒ C) → Functor R (A ⇒ B) → Bifunctor L R (A ⇒ C)
  _∘_ {A} {B} {C} F G = reduce-× {D₁ = B ⇒ C} {D₂ = A ⇒ B} —∘— F G
  field
    .assoc : ∀ {A B C D : Obj} → ((—∘— ∘ idF) ∘F assocʳ (C ⇒ D) (B ⇒ C) (A ⇒ B)) ≡F (idF ∘ —∘—)
    .identityˡ : {A B : Obj} → (id {B} ∘ idF {C = A ⇒ B}) ≡F πʳ {C = ⊤} {A ⇒ B}
    .identityʳ : {A B : Obj} → (idF {C = A ⇒ B} ∘ id {A}) ≡F πˡ {C = A ⇒ B} {⊤}

  -- convenience?
  module _⇒_ (A B : Obj) = Category (A ⇒ B)
  open _⇒_ public using () renaming (Obj to _⇒₁_)

  private module imp⇒ {X Y : Obj} = Category (X ⇒ Y)
  open imp⇒ public using () renaming (_⇒_ to _⇒₂_; id to id₂; _∘_ to _•_; assoc to vassoc′; identityˡ to videntityˡ′; identityʳ to videntityʳ′; ∘-resp-≡ to •-resp-≡′; ∘-resp-≡ˡ to •-resp-≡′ˡ; ∘-resp-≡ʳ to •-resp-≡′ʳ; hom-setoid to hom₂′-setoid; _≡_ to _≡′_; equiv to equiv′; module Equiv to Equiv′)

  module Equiv {X Y : Obj} = Heterogeneous (X ⇒ Y)
  open Equiv public using () renaming (_∼_ to _≡_; ≡⇒∼ to loosely)

  id₁ : ∀ {A} → A ⇒₁ A
  id₁ {A} = Functor.F₀ (id {A}) unit

  id₁₂ : ∀ {A} → id₁ {A} ⇒₂ id₁ {A}
  id₁₂ {A} = id₂ {A = id₁ {A}}

  infixr 9 _∘₁_
  _∘₁_ : ∀ {A B C} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘₁_ = curry (Functor.F₀ —∘—)

  -- horizontal composition
  infixr 9 _∘₂_
  _∘₂_ : ∀ {A B C} {g g′ : B ⇒₁ C} {f f′ : A ⇒₁ B} (β : g ⇒₂ g′) (α : f ⇒₂ f′) → (g ∘₁ f) ⇒₂ (g′ ∘₁ f′)
  _∘₂_ = curry (Functor.F₁ —∘—)

  .∘₂-resp-≡′ : ∀ {A B C} {f h : B ⇒₁ C} {g i : A ⇒₁ B} {α γ : f ⇒₂ h} {β δ : g ⇒₂ i} → α ≡′ γ → β ≡′ δ → α ∘₂ β ≡′ γ ∘₂ δ
  ∘₂-resp-≡′ = curry (Functor.F-resp-≡ —∘—)

  .∘₂-resp-≡ : ∀ {A B C} {f f′ h h′ : B ⇒₁ C} {g g′ i i′ : A ⇒₁ B} {α : f ⇒₂ h} {γ : f′ ⇒₂ h′} {β : g ⇒₂ i} {δ : g′ ⇒₂ i′} → α ≡ γ → β ≡ δ → (α ∘₂ β) ≡ (γ ∘₂ δ)
  ∘₂-resp-≡ (loosely a) (loosely b) = loosely (∘₂-resp-≡′ a b)

  -- left whiskering
  infixl 9 _◃_
  _◃_ : ∀ {A B C} {g g′ : B ⇒₁ C} → g ⇒₂ g′ → (f : A ⇒₁ B) → (g ∘₁ f) ⇒₂ (g′ ∘₁ f)
  β ◃ f = β ∘₂ id₂

  -- right whiskering
  infixr 9 _▹_
  _▹_ : ∀ {A B C} (g : B ⇒₁ C) → {f f′ : A ⇒₁ B} → f ⇒₂ f′ → (g ∘₁ f) ⇒₂ (g ∘₁ f′)
  g ▹ α = id₂ ∘₂ α

  private
    ≡F-on-objects : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) → (F ≡F G) → (X : Category.Obj C) → Functor.F₀ F X ≣ Functor.F₀ G X
    ≡F-on-objects {C = C} F G eq X with Functor.F₀ F X | Functor.F₁ F (Category.id C {X}) | eq (Category.id C {X})
    ≡F-on-objects {C = C} F G eq X | ._ | _ | Heterogeneous.≡⇒∼ _ = ≣-refl

  private
    module Laws1A {A B} {f : A ⇒₁ B} where
      .assoc₁ : ∀ {C D} {g : B ⇒₁ C} {h : C ⇒₁ D} → ((h ∘₁ g) ∘₁ f) ≣ (h ∘₁ (g ∘₁ f))
      assoc₁ {C} {D} {g} {h} = ≡F-on-objects ((—∘— ∘ idF) ∘F assocʳ (C ⇒ D) (B ⇒ C) (A ⇒ B)) (idF ∘ —∘—) assoc (h , g , f)

      .identity₁ˡ : {- ∀ {A B} {f : A ⇒₁ B} → -} id₁ ∘₁ f ≣ f
      identity₁ˡ = ≡F-on-objects (id {B} ∘ idF {C = A ⇒ B}) (πʳ {C = ⊤} {A ⇒ B}) identityˡ (unit , f)

  .identity₁ʳ : ∀ {A B} {f : A ⇒₁ B} → f ∘₁ id₁ ≣ f
  identity₁ʳ {A} {B} {f} = ≡F-on-objects (idF {C = A ⇒ B} ∘ id {A}) (πˡ {C = A ⇒ B} {⊤}) identityʳ (f , unit)


  .vassoc : ∀ {A B} {f g h i : A ⇒₁ B} {η : f ⇒₂ g} {θ : g ⇒₂ h} {ι : h ⇒₂ i} → ((ι • θ) • η) ≡ (ι • (θ • η))
  vassoc = loosely vassoc′

  .hidentityˡ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (id₁₂ ∘₂ η) ≡ η
  hidentityˡ {A} {B} {f} {f′} {η} = Equiv.trans (loosely (∘₂-resp-≡′ (Equiv′.sym (Functor.identity id)) Equiv′.refl)) (identityˡ (unit , η))

  .hidentityʳ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (η ∘₂ id₁₂) ≡ η
  hidentityʳ {A} {B} {f} {f′} {η} = Equiv.trans (loosely (∘₂-resp-≡′ Equiv′.refl (Equiv′.sym (Functor.identity id)))) (identityʳ (η , unit))

  .im-id₂-closed-under-∘₂′ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → id₂ {A = g} ∘₂ id₂ {A = f} ≡′ id₂ {A = g ∘₁ f}
  im-id₂-closed-under-∘₂′ = Functor.identity —∘—

  .im-id₂-closed-under-∘₂ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → (id₂ {A = g} ∘₂ id₂ {A = f}) ≡ id₂ {A = g ∘₁ f}
  im-id₂-closed-under-∘₂ = loosely im-id₂-closed-under-∘₂′

  .lidentityˡ′ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → id₂ {A = g} ◃ f ≡′ id₂
  lidentityˡ′ = Functor.identity —∘—

  .lidentityˡ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → (id₂ {A = g} ◃ f) ≡ id₂ {A = g ∘₁ f}
  lidentityˡ = loosely lidentityˡ′

  .ridentityʳ′ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → g ▹ id₂ {A = f} ≡′ id₂
  ridentityʳ′ = Functor.identity —∘—

  .ridentityʳ : ∀ {A B C} {f : A ⇒₁ B} {g : B ⇒₁ C} → (g ▹ id₂ {A = f}) ≡ id₂ {A = g ∘₁ f}
  ridentityʳ = loosely ridentityʳ′

  -- .lidentityʳ′ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (η ◃ id₁) ≡′ η
  -- lidentityʳ′ = ?

  .lidentityʳ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (η ◃ id₁) ≡ η
  lidentityʳ {η = η} = Equiv.trans (∘₂-resp-≡ Equiv.refl (Equiv.sym (loosely (Functor.identity id)))) (identityʳ (η , unit))

  -- .ridentityˡ′ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (id₁ ▹ η) ≡′ η
  -- ridentityˡ′ = ?

  .ridentityˡ : ∀ {A B} {f f′ : A ⇒₁ B} {η : f ⇒₂ f′} → (id₁ ▹ η) ≡ η
  ridentityˡ {η = η} = Equiv.trans (∘₂-resp-≡ (Equiv.sym (loosely (Functor.identity id))) Equiv.refl) (identityˡ (unit , η))

  .interchange′ : ∀ {A B C} {f g h : A ⇒₁ B} {i j k : B ⇒₁ C} {α : f ⇒₂ g} {β : g ⇒₂ h} {γ : i ⇒₂ j} {δ : j ⇒₂ k} → ((δ • γ) ∘₂ (β • α)) ≡′ ((δ ∘₂ β) • (γ ∘₂ α))
  interchange′ = Functor.homomorphism —∘—

  .interchange : ∀ {A B C} {f g h : A ⇒₁ B} {i j k : B ⇒₁ C} {α : f ⇒₂ g} {β : g ⇒₂ h} {γ : i ⇒₂ j} {δ : j ⇒₂ k} → ((δ • γ) ∘₂ (β • α)) ≡ ((δ ∘₂ β) • (γ ∘₂ α))
  interchange = loosely interchange′

  .lvdistrib′ : ∀ {A B C} {f : A ⇒₁ B} {g h i : B ⇒₁ C} {η : g ⇒₂ h} {θ : h ⇒₂ i} → (θ • η) ◃ f ≡′ ((θ ◃ f) • (η ◃ f))
  lvdistrib′ = Equiv′.trans (∘₂-resp-≡′ Equiv′.refl (Equiv′.sym videntityˡ′)) interchange′

  .lvdistrib : ∀ {A B C} {f : A ⇒₁ B} {g h i : B ⇒₁ C} {η : g ⇒₂ h} {θ : h ⇒₂ i} → ((θ • η) ◃ f) ≡ ((θ ◃ f) • (η ◃ f))
  lvdistrib = loosely lvdistrib′

  .rvdistrib′ : ∀ {A B C} {f g h : A ⇒₁ B} {i : B ⇒₁ C} {η : f ⇒₂ g} {θ : g ⇒₂ h} → (i ▹ (θ • η)) ≡′ ((i ▹ θ) • (i ▹ η))
  rvdistrib′ = Equiv′.trans (∘₂-resp-≡′ (Equiv′.sym videntityˡ′) Equiv′.refl) interchange′

  .rvdistrib : ∀ {A B C} {f g h : A ⇒₁ B} {i : B ⇒₁ C} {η : f ⇒₂ g} {θ : g ⇒₂ h} → (i ▹ (θ • η)) ≡ ((i ▹ θ) • (i ▹ η))
  rvdistrib = loosely rvdistrib′

  -- XXX mixed assocs still need proving
  {-
  -- XXX not well-typed without a subst or something
  -- .lhassoc′ : ∀ {A B C D} {f : A ⇒₁ B} {g : B ⇒₁ C} {h i : C ⇒₁ D} {η : h ⇒₂ i} → (η ◃ (g ∘₁ f)) ≡′ {!((η ◃ g) ◃ f)!}
  -- lhassoc′ = {!!}

  .lhassoc : ∀ {A B C D} {f : A ⇒₁ B} {g : B ⇒₁ C} {h i : C ⇒₁ D} {η : h ⇒₂ i} → (η ◃ (g ∘₁ f)) ≡ ((η ◃ g) ◃ f)
  lhassoc = {!!}

  -- XXX ditto
  -- .rlassoc′ : ∀ {A B C D} {f : A ⇒₁ B} {g h : B ⇒₁ C} {i : C ⇒₁ D} {η : g ⇒₂ h} → (i ▹ (η ◃ f)) ≡′ {!((i ▹ η) ◃ f)!}
  -- rlassoc′ = {!!}

  .rlassoc : ∀ {A B C D} {f : A ⇒₁ B} {g h : B ⇒₁ C} {i : C ⇒₁ D} {η : g ⇒₂ h} → (i ▹ (η ◃ f)) ≡ ((i ▹ η) ◃ f)
  rlassoc = {!!}

  -- XXX tritto
  -- .hrassoc′ : ∀ {A B C D} {f g : A ⇒₁ B} {h : B ⇒₁ C} {i : C ⇒₁ D} {η : f ⇒₂ g} → (i ▹ (h ▹ η)) ≡′ {!((i ∘₁ h) ▹ η)!}
  -- hrassoc′ = {!!}

  .hrassoc : ∀ {A B C D} {f g : A ⇒₁ B} {h : B ⇒₁ C} {i : C ⇒₁ D} {η : f ⇒₂ g} → (i ▹ (h ▹ η)) ≡ ((i ∘₁ h) ▹ η)
  hrassoc = {!!}
  -}

  .lrsmoosh′ : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((θ ◃ g) • (h ▹ η)) ≡′ (θ ∘₂ η)
  lrsmoosh′ = Equiv′.trans (Equiv′.sym interchange′) (∘₂-resp-≡′ videntityʳ′ videntityˡ′)

  .lrsmoosh : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((θ ◃ g) • (h ▹ η)) ≡ (θ ∘₂ η)
  lrsmoosh = loosely lrsmoosh′

  .rlsmoosh′ : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((i ▹ η) • (θ ◃ f)) ≡′ (θ ∘₂ η)
  rlsmoosh′ = Equiv′.trans (Equiv′.sym interchange′) (∘₂-resp-≡′ videntityˡ′ videntityʳ′)

  .rlsmoosh : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((i ▹ η) • (θ ◃ f)) ≡ (θ ∘₂ η)
  rlsmoosh = loosely rlsmoosh′

  .lrexch′ : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((i ▹ η) • (θ ◃ f)) ≡′ ((θ ◃ g) • (h ▹ η))
  lrexch′ = Equiv′.trans rlsmoosh′ (Equiv′.sym lrsmoosh′)

  .lrexch : ∀ {A B C} {f g : A ⇒₁ B} {h i : B ⇒₁ C} {η : f ⇒₂ g} {θ : h ⇒₂ i} → ((i ▹ η) • (θ ◃ f)) ≡ ((θ ◃ g) • (h ▹ η))
  lrexch = loosely lrexch′

  module Hom₁Reasoning = ≣-reasoning

  module Hom₂′Reasoning {A B : Obj} {f g : A ⇒₁ B} where
    open imp⇒.HomReasoning {A} {B} {f} {g} public renaming (_⟩∘⟨_ to _⟩•⟨_)

    -- XXX won't work if Hom₂′Reasoning is frozen
    infixr 4 _⟩∘₂⟨_
    ._⟩∘₂⟨_ : ∀ {C} {h i : C ⇒₁ A} {α β : f ⇒₂ g} {γ δ : h ⇒₂ i} → α ≡′ β → γ ≡′ δ → (α ∘₂ γ) ≡′ (β ∘₂ δ)
    _⟩∘₂⟨_ = ∘₂-resp-≡′
