{-# OPTIONS --universe-polymorphism #-}
module Categories.Cocones where

open import Level

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Category
open import Categories.Functor hiding (_≡_; equiv; id; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Categories.Cocone

record CoconeMorphism {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} {F : Functor J C} (c₁ c₂ : Cocone F) : Set (a ⊔ o′ ⊔ a′) where
  module c₁ = Cocone c₁
  module c₂ = Cocone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C [ c₁.N , c₂.N ]
    .commute : ∀ {X} → f ∘ c₁.ψ X ≡ c₂.ψ X

Coconesᵉ : ∀ {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} (F : Functor J C) → EasyCategory (o ⊔ a ⊔ o′ ⊔ a′) (a ⊔ o′ ⊔ a′) a
Coconesᵉ {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; compose = _∘′_
  ; id = record { f = id; commute = identityˡ }
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; promote = promote′
  ; REFL = Equiv.refl
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

  promote′ : ∀ {A B : Obj′} (f f′ : Hom′ A B) → f ≡′ f′ → f ≣ f′
  promote′ {A} {B} g g′ g≡g′ = lemma (f g′) g≡g′
    where
    lemma : ∀ f′ → (f≣f′ : f g ≣ f′) → g ≣ record { f = f′; commute = ≣-subst (λ f″ → ∀ {X} → f″ ∘ ψ A X ≣ ψ B X) f≣f′ (CoconeMorphism.commute g) }
    lemma .(f g) ≣-refl = ≣-refl 

Cocones : ∀ {o a} {o′ a′} {C : Category o a} {J : Category o′ a′} (F : Functor J C) → Category (o ⊔ a ⊔ o′ ⊔ a′) (a ⊔ o′ ⊔ a′)
Cocones F = EASY Coconesᵉ F
