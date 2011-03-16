{-# OPTIONS --universe-polymorphism #-}
module Category.Grothendieck where

open import Support
open import Category
open import Category.Functor
open import Category.Agda

-- Break into modules Strict and Weak using Sets and Setoids?
Grothendieck : ∀ {o ℓ e o′} {C : Category o ℓ e} → Functor C (Sets o′) → Category _ _ _
Grothendieck {o′ = o′} {C = C} F = record 
  { Obj = Obj′
  ; Hom = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = Category.id C , Functor.identity F
  ; assoc = Category.assoc C
  ; identityˡ = Category.identityˡ C
  ; identityʳ = Category.identityʳ C
  ; equiv = record
    { refl = IsEquivalence.refl (Category.equiv C)
    ; sym = IsEquivalence.sym (Category.equiv C)
    ; trans = IsEquivalence.trans (Category.equiv C)
    }
  ; ∘-resp-≡ = Category.∘-resp-≡ C
  }
  where
  Obj′ = Σ (Category.Obj C) (Functor.F₀ F)
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ′ (Category.Hom C c₁ c₂) (λ f → Functor.F₁ F f x₁ ≣ x₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  (f , pf₁) ≡′ (g , pf₂) = Category._≡_ C f g

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {X} {Y} {Z} (f , pf₁) (g , pf₂) = (Category._∘_ C f g) , pf
    where
    -- This could be a lot prettier...
    .pf : Functor.F₁ F (Category._∘_ C f g) (proj₂ X) ≣ proj₂ Z
    pf = ≣-trans (≣-sym (≣-trans (≣-cong (Functor.F₁ F f) (≣-sym pf₂)) (≣-sym pf₁))) (Functor.homomorphism F)

