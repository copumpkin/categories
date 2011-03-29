{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Algebras where

open import Support hiding (⊥)
open import Category
open import Category.Functor hiding (_≡_; id; _∘_; equiv; assoc; identityˡ; identityʳ; ∘-resp-≡)
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
  Hom′ (A , α) (B , β) = Σ′ (Hom A B) (λ m → m ∘ α ≡ β ∘ F₁ m)

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



open import Category.Object.Initial

module Lambek {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} (I : Initial (F-Algebras F)) where
  module C = Category.Category C
  module FA = Category.Category (F-Algebras F) renaming (_∘_ to _∘FA_; _≡_ to _≡FA_)
  open Functor F
  import Category.Morphisms as Morphisms
  open Morphisms C
  open Initial (F-Algebras F) I
  open F-Algebra ⊥

  lambek : A ≅ F₀ A
  lambek = record 
    { f = f′
    ; g = g′
    ; iso = iso′
    }
    where
    f′ : C.Hom A (F₀ A)
    f′ = proj₁′ (! {lift ⊥}) 

    g′ : C.Hom (F₀ A) A
    g′ = α

    .iso′ : Iso f′ g′
    iso′ = record 
      { isoˡ = isoˡ′
      ; isoʳ = begin
                 f′ ∘ g′
               ≈⟨ proj₂′ (! {lift ⊥}) ⟩
                 F₁ g′ ∘ F₁ f′
               ≈⟨ sym homomorphism ⟩
                 F₁ (g′ ∘ f′)
               ≈⟨ F-resp-≡ isoˡ′ ⟩
                 F₁ id
               ≈⟨ identity ⟩
                 id
               ∎
      }
      where
      open C
      open FA hiding (id)
      open IsEquivalence C.equiv
      open SetoidReasoning C.hom-setoid

      isoˡ′ = ⊥-id ((g′ , IsEquivalence.refl C.equiv) ∘FA !)

open Lambek public