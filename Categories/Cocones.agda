{-# OPTIONS --universe-polymorphism #-}
module Categories.Cocones where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_∘_; _≡_; equiv; id; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Categories.Cocone

record CoconeMorphism {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {F : Functor J C} (c₁ c₂ : Cocone F) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) where
  module c₁ = Cocone c₁
  module c₂ = Cocone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C [ c₁.N , c₂.N ]
    .commute : ∀ {X} → f ∘ c₁.ψ X ≡ c₂.ψ X

Cocones : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′) (ℓ ⊔ e ⊔ o′ ⊔ ℓ′) e
Cocones {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = record { f = id; commute = identityˡ }
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
  open Cocone
  open CoconeMorphism
  open Functor F

  infixr 9 _∘′_
  infix  4 _≡′_

  Obj′ = Cocone F

  Hom′ : Obj′ → Obj′ → Set _
  Hom′ = CoconeMorphism

  _≡′_ : ∀ {A B} → Hom′ A B → Hom′ A B → Set _
  F ≡′ G = f F ≡ f G

  _∘′_ : ∀ {A B C} → Hom′ B C → Hom′ A B → Hom′ A C
  _∘′_ {A} {B} {C} F G = record 
    { f = f F ∘ f G
    ; commute = commute′
    }
    where
    .commute′ : ∀ {X} → (f F ∘ f G) ∘ ψ A X ≡ ψ C X
    commute′ {X} = 
        begin
          (f F ∘ f G) ∘ ψ A X
        ↓⟨ assoc ⟩
          f F ∘ (f G ∘ ψ A X)
        ↓⟨ ∘-resp-≡ʳ (CoconeMorphism.commute G) ⟩
          f F ∘ ψ B X
        ↓⟨ CoconeMorphism.commute F ⟩
          ψ C X
        ∎
      where
      open HomReasoning

