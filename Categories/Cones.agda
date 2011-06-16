{-# OPTIONS --universe-polymorphism #-}
module Categories.Cones where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_∘_; _≡_; equiv; id; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Categories.Cone

record ConeMorphism {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {F : Functor J C} (c₁ c₂ : Cone F) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  module c₁ = Cone c₁
  module c₂ = Cone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C [ c₁.N , c₂.N ]
    .commute : ∀ {X} → c₁.ψ X ≡ c₂.ψ X ∘ f

Cones : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) e
Cones {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = record { f = id; commute = Equiv.sym identityʳ }
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record 
    { refl = Equiv.refl
    ; sym = Equiv.sym
    ; trans = Equiv.trans
    }
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  open Category C
  open Cone
  open ConeMorphism
  open Functor F

  infixr 9 _∘′_
  infix  4 _≡′_

  Obj′ = Cone F

  Hom′ : Obj′ → Obj′ → Set _
  Hom′ = ConeMorphism

  _≡′_ : ∀ {A B} → Hom′ A B → Hom′ A B → Set _
  F ≡′ G = f F ≡ f G

  _∘′_ : ∀ {A B C} → Hom′ B C → Hom′ A B → Hom′ A C
  _∘′_ {A} {B} {C} F G = record 
    { f = f F ∘ f G
    ; commute = commute′
    }
    where
    .commute′ : ∀ {X} → ψ A X ≡ ψ C X ∘ (f F ∘ f G)
    commute′ {X} = 
        begin
          ψ A X
        ↓⟨ ConeMorphism.commute G ⟩
          ψ B X ∘ f G
        ↓⟨ ∘-resp-≡ˡ (ConeMorphism.commute F) ⟩
          (ψ C X ∘ f F) ∘ f G
        ↓⟨ assoc ⟩
          ψ C X ∘ (f F ∘ f G)
        ∎
      where
      open HomReasoning

