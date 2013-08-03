{-# OPTIONS --universe-polymorphism #-}
module Categories.Grothendieck where

open import Relation.Binary using (Rel)
open import Data.Product using (Σ; _,_; proj₂; _×_)

open import Categories.Support.PropositionalEquality
open import Categories.Support.IProduct
open import Categories.Category
open import Categories.Functor using (Functor; module Functor; ≡⇒≣)
open import Categories.Agda

-- TODO: don't use sigmas
-- Break into modules Strict and Weak using Sets and Setoids?
Grothendieck : ∀ {o ℓ e o′} {C : Category o ℓ e} → Functor C (Sets o′) → Category _ _ _
Grothendieck {o′ = o′} {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id , identity
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  open Category C
  open Equiv
  open Functor F

  Obj′ = Σ Obj F₀
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ′ (c₁ ⇒ c₂) (λ f → F₁ f x₁ ≣ x₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  (f , pf₁) ≡′ (g , pf₂) = f ≡ g

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {X} {Y} {Z} (f , pf₁) (g , pf₂) = (f ∘ g) , pf
    where
    -- This could be a lot prettier...
    .pf : F₁ (f ∘ g) (proj₂ X) ≣ proj₂ Z
    pf = ≣-trans homomorphism (≣-sym (≣-trans (≣-sym pf₁) (≣-cong (F₁ f) (≣-sym pf₂))))


open import Categories.Categories

Grothendieck2 : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} → Functor C (Categories o′ ℓ′ e′) → Category _ _ _
Grothendieck2 {o′ = o′} {ℓ′} {e′} {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id , {!!}
  ; assoc = {! assoc !}
  ; identityˡ = {! identityˡ !}
  ; identityʳ = {! identityʳ !}
  ; equiv = {! record
    { refl = refl
    ; sym = sym
    ; trans = trans
    } !}
  ; ∘-resp-≡ = {! ∘-resp-≡ !}
  }
  where
  open Category C
  open Equiv
  open Functor F

  Obj′ = Σ Obj (\ c -> Category.Obj (F₀ c))
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ (c₁ ⇒ c₂) (λ f → Functor.F₀ (F₁ f) x₁ Fc₂.⇒ x₂)
    where
      module Fc₂ = Category (F₀ c₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  _≡′_ {c₁ , x₁} {c₂ , x₂} (f , α) (g , β) = f ≡ g × α Fc₂.∼ β
    where
      module Fc₂ = Heterogeneous (F₀ c₂)

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {cx , xx} {Y} {cz , xz} (f , α) (g , β) = (f ∘ g) , γ 
   where 
    module Fcz = Category (F₀ cz)

    -- This could be a lot prettier...
    postulate ≣-relevant : ∀ {l} {A : Set l} {X Y : A} -> .(X ≣ Y) -> X ≣ Y

    γ : Functor.F₀ (F₁ (f ∘ g)) xx Fcz.⇒ xz
    γ rewrite ≣-relevant (≡⇒≣ (F₁ (f ∘ g)) (Categories _ _ _ [ F₁ f ∘ F₁ g ]) (homomorphism {f = g} {g = f}) xx)
       = α Fcz.∘ Functor.F₁ (F₁ f) β
