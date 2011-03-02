{-# OPTIONS --universe-polymorphism #-}
module Category.Cones where

open import Support
open import Category
open import Category.Functor hiding (_∘_; _≡_; equiv; id; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Category.Cone

record ConeMorphism {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {F : Functor J C} (c₁ c₂ : Cone F) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  module c₁ = Cone c₁
  module c₂ = Cone c₂
  module C = Category.Category C
  module J = Category.Category J
  open C
  field
    f : C.Hom c₁.N c₂.N
    .commute : ∀ {X} → c₁.ψ X ≡ c₂.ψ X ∘ f

Cones : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) e
Cones {C = C} F = record 
  { Obj = Obj′
  ; Hom = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = record { f = id; commute = IsEquivalence.sym equiv identityʳ }
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record 
    { refl = IsEquivalence.refl equiv
    ; sym = IsEquivalence.sym equiv
    ; trans = IsEquivalence.trans equiv
    }
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  open Category.Category C
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
        ≈⟨ ConeMorphism.commute G ⟩
          ψ B X ∘ f G
        ≈⟨ ∘-resp-≡ˡ (ConeMorphism.commute F) ⟩
          (ψ C X ∘ f F) ∘ f G
        ≈⟨ assoc ⟩
          ψ C X ∘ (f F ∘ f G)
        ∎
      where
      open SetoidReasoning hom-setoid

