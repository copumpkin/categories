{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Algebras where

open import Support
open import Category
open import Category.Functor hiding (_≡_; id; _∘_; equiv)
open import Category.Functor.Algebra

F-Algebras : ∀ {o ℓ e} {C : Category o ℓ e} → Endofunctor C → Category (ℓ ⊔ o) (e ⊔ ℓ) e
F-Algebras {C = C} F = record 
  { Obj = Obj′
  ; Hom = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
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
  open Functor F
  Obj′ = F-Algebra F

  Hom′ : (A B : Obj′) → Set _
  Hom′ (A , α) (B , β) = Σ′ (Hom A B) (λ m → CommutativeSquare α (F₁ m) m β)

  _≡′_ : ∀ {A B} (f g : Hom′ A B) → Set _
  f ≡′ g = proj₁′ f ≡ proj₁′ g

  -- FIXME: this proj₁′ stuff is fugly, but Agda won't let me pattern match on the constructor :/
  _∘′_ : ∀ {A B C} → Hom′ B C → Hom′ A B → Hom′ A C
  _∘′_ {A} {B} {C} f g = proj₁′ f ∘ proj₁′ g , pf
    where
    module A = F-Algebra A
    module B = F-Algebra B
    module C = F-Algebra C

    .pf : (proj₁′ f ∘ proj₁′ g) ∘ A.α ≡ C.α ∘ (F₁ (proj₁′ f ∘ proj₁′ g))
    pf = begin
           (proj₁′ f ∘ proj₁′ g) ∘ A.α
         ≈⟨ assoc ⟩
           proj₁′ f ∘ (proj₁′ g ∘ A.α)
         ≈⟨ ∘-resp-≡ʳ (proj₂′ g) ⟩
           proj₁′ f ∘ (B.α ∘ F₁ (proj₁′ g))
         ≈⟨ sym assoc ⟩
           (proj₁′ f ∘ B.α) ∘ F₁ (proj₁′ g)
         ≈⟨ ∘-resp-≡ˡ (proj₂′ f) ⟩
           (C.α ∘ F₁ (proj₁′ f)) ∘ F₁ (proj₁′ g)
         ≈⟨ assoc ⟩
           C.α ∘ (F₁ (proj₁′ f) ∘ F₁ (proj₁′ g))
         ≈⟨ sym (∘-resp-≡ʳ homomorphism) ⟩
           C.α ∘ (F₁ (proj₁′ f ∘ proj₁′ g))
         ∎
      where
      open IsEquivalence equiv
      open SetoidReasoning hom-setoid

  id′ : ∀ {A} → Hom′ A A
  id′ {A} = id , pf
    where
    module A = F-Algebra A

    .pf : id ∘ A.α ≡ A.α ∘ F₁ id
    pf = begin
           id ∘ A.α
         ≈⟨ identityˡ ⟩
           A.α
         ≈⟨ sym identityʳ ⟩
           A.α ∘ id
         ≈⟨ sym (∘-resp-≡ʳ identity) ⟩
           A.α ∘ F₁ id
         ∎
      where
      open IsEquivalence equiv
      open SetoidReasoning hom-setoid