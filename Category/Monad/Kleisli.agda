{-# OPTIONS --universe-polymorphism #-}
module Category.Monad.Kleisli where

open import Support
open import Category
open import Category.Functor hiding (_≡_; _∘_; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Category.NaturalTransformation hiding (_≡_)
open import Category.Monad

Kleisli : ∀ {o ℓ e} {C : Category o ℓ e} → Monad C → Category o ℓ e
Kleisli {C = C} M = record 
  { Obj = Obj
  ; Hom = λ A B → Hom A (F₀ B)
  ; _≡_ = _≡_
  ; _∘_ = λ f g → (μ.η _ ∘ Functor.F₁ F f) ∘ g
  ; id = η.η _
  ; assoc = assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; equiv = Category.equiv C
  ; ∘-resp-≡ = λ f≡h g≡i → ∘-resp-≡ (∘-resp-≡ (IsEquivalence.refl C.equiv) (F-resp-≡ f≡h)) g≡i
  }
  where
  module M = Monad M
  open M
  module μ = NaturalTransformation μ
  module η = NaturalTransformation η
  open Functor F
  module C = Category.Category C
  open C

  -- I should really find a better module layout that saves me from having to open a bunch of stuff every time or name things in full
  .assoc′ : ∀ {A B C D} {f : Hom A (F₀ B)} {g : Hom B (F₀ C)} {h : Hom C (F₀ D)} →
      (NaturalTransformation.η μ D ∘ (F₁ ((NaturalTransformation.η μ D ∘ F₁ h) ∘ g))) ∘ f ≡
      (NaturalTransformation.η μ D ∘ F₁ h) ∘ ((NaturalTransformation.η μ C ∘ F₁ g) ∘ f)
  assoc′ {A} {B} {C} {D} {f} {g} {h} =
      begin
        (NaturalTransformation.η μ D ∘ F₁ ((NaturalTransformation.η μ D ∘ F₁ h) ∘ g)) ∘ f
      ≈⟨ C.assoc ⟩
        NaturalTransformation.η μ D ∘ (F₁ ((NaturalTransformation.η μ D ∘ F₁ h) ∘ g) ∘ f)
      ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (F-resp-≡ C.assoc)) ⟩
        NaturalTransformation.η μ D ∘ (F₁ (NaturalTransformation.η μ D ∘ (F₁ h ∘ g)) ∘ f)
      ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ homomorphism) ⟩
        NaturalTransformation.η μ D ∘ ((F₁ (NaturalTransformation.η μ D) ∘ F₁ (F₁ h ∘ g)) ∘ f)
      ≈⟨ ∘-resp-≡ʳ C.assoc ⟩
        NaturalTransformation.η μ D ∘ (F₁ (NaturalTransformation.η μ D) ∘ (F₁ (F₁ h ∘ g) ∘ f))
      ≈⟨ sym C.assoc ⟩
        (NaturalTransformation.η μ D ∘ F₁ (NaturalTransformation.η μ D)) ∘ (F₁ (F₁ h ∘ g) ∘ f)
      ≈⟨ ∘-resp-≡ˡ M.assoc ⟩
        (NaturalTransformation.η μ D ∘ NaturalTransformation.η μ (F₀ D)) ∘ (F₁ (F₁ h ∘ g) ∘ f)
      ≈⟨ C.assoc ⟩
        NaturalTransformation.η μ D ∘ (NaturalTransformation.η μ (F₀ D) ∘ (F₁ (F₁ h ∘ g) ∘ f))
      ≈⟨ sym (∘-resp-≡ʳ C.assoc) ⟩
        NaturalTransformation.η μ D ∘ ((NaturalTransformation.η μ (F₀ D) ∘ F₁ (F₁ h ∘ g)) ∘ f)
      ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (∘-resp-≡ʳ homomorphism)) ⟩
        NaturalTransformation.η μ D ∘ ((NaturalTransformation.η μ (F₀ D) ∘ (F₁ (F₁ h) ∘ F₁ g)) ∘ f)
      ≈⟨ sym (∘-resp-≡ʳ (∘-resp-≡ˡ C.assoc)) ⟩
        NaturalTransformation.η μ D ∘ (((NaturalTransformation.η μ (F₀ D) ∘ F₁ (F₁ h)) ∘ F₁ g) ∘ f)
      ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (∘-resp-≡ˡ (NaturalTransformation.commute μ h))) ⟩
        NaturalTransformation.η μ D ∘ (((F₁ h ∘ NaturalTransformation.η μ C) ∘ F₁ g) ∘ f)
      ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ C.assoc) ⟩
        NaturalTransformation.η μ D ∘ ((F₁ h ∘ (NaturalTransformation.η μ C ∘ F₁ g)) ∘ f)
      ≈⟨ ∘-resp-≡ʳ C.assoc ⟩
        NaturalTransformation.η μ D ∘ (F₁ h ∘ ((NaturalTransformation.η μ C ∘ F₁ g) ∘ f))
      ≈⟨ sym C.assoc ⟩
        (NaturalTransformation.η μ D ∘ F₁ h) ∘ ((NaturalTransformation.η μ C ∘ F₁ g) ∘ f)
      ∎
    where
    open IsEquivalence C.equiv
    open SetoidReasoning hom-setoid


  .identityˡ′ : ∀ {A B} {f : Hom A (F₀ B)} → (NaturalTransformation.η μ B ∘ F₁ (NaturalTransformation.η η B)) ∘ f ≡ f
  identityˡ′ {A} {B} {f} = 
      begin
        (NaturalTransformation.η μ B ∘ F₁ (NaturalTransformation.η η B)) ∘ f
      ≈⟨ ∘-resp-≡ˡ M.identityˡ ⟩
        C.id ∘ f
      ≈⟨ C.identityˡ ⟩
        f
      ∎
    where
    open SetoidReasoning hom-setoid

  .identityʳ′ : ∀ {A B} {f : Hom A (F₀ B)} → (NaturalTransformation.η μ B ∘ F₁ f) ∘ NaturalTransformation.η η A ≡ f
  identityʳ′ {A} {B} {f} = 
      begin
        (NaturalTransformation.η μ B ∘ F₁ f) ∘ NaturalTransformation.η η A
      ≈⟨ C.assoc ⟩
        NaturalTransformation.η μ B ∘ (F₁ f ∘ NaturalTransformation.η η A)
      ≈⟨ sym (∘-resp-≡ʳ (η.commute f)) ⟩
        NaturalTransformation.η μ B ∘ (NaturalTransformation.η η (Functor.F₀ F B) ∘ f)
      ≈⟨ sym C.assoc ⟩
        (NaturalTransformation.η μ B ∘ NaturalTransformation.η η (Functor.F₀ F B)) ∘ f
      ≈⟨ ∘-resp-≡ˡ M.identityʳ ⟩
        C.id ∘ f
      ≈⟨ C.identityˡ ⟩
        f
      ∎
    where
    open IsEquivalence C.equiv
    open SetoidReasoning hom-setoid
