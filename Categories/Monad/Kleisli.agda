{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad.Kleisli where

open import Categories.Category
open import Categories.Functor using (Functor; module Functor)
open import Categories.NaturalTransformation hiding (_≡_; equiv; id)
open import Categories.Monad

Kleisli : ∀ {o ℓ e} {C : Category o ℓ e} → Monad C → Category o ℓ e
Kleisli {C = C} M = record 
  { Obj = Obj
  ; _⇒_ = λ A B → (A ⇒ F₀ B)
  ; _≡_ = _≡_
  ; _∘_ = λ f g → (μ.η _ ∘ F₁ f) ∘ g
  ; id = η.η _
  ; assoc = assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; equiv = equiv
  ; ∘-resp-≡ = λ f≡h g≡i → ∘-resp-≡ (∘-resp-≡ refl (F-resp-≡ f≡h)) g≡i
  }
  where
  module M = Monad M
  open M using (μ; η; F)
  module μ = NaturalTransformation μ
  module η = NaturalTransformation η
  open Functor F
  open Category C
  open Equiv

  .assoc′ : ∀ {A B C D} {f : A ⇒ F₀ B} {g : B ⇒ F₀ C} {h : C ⇒ F₀ D} 
          → (μ.η D ∘ (F₁ ((μ.η D ∘ F₁ h) ∘ g))) ∘ f ≡ (μ.η D ∘ F₁ h) ∘ ((μ.η C ∘ F₁ g) ∘ f)
  assoc′ {A} {B} {C} {D} {f} {g} {h} =
      begin
        (μ.η D ∘ F₁ ((μ.η D ∘ F₁ h) ∘ g)) ∘ f
      ↓⟨ assoc ⟩
        μ.η D ∘ (F₁ ((μ.η D ∘ F₁ h) ∘ g) ∘ f)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (F-resp-≡ assoc)) ⟩
        μ.η D ∘ (F₁ (μ.η D ∘ (F₁ h ∘ g)) ∘ f)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ homomorphism) ⟩
        μ.η D ∘ ((F₁ (μ.η D) ∘ F₁ (F₁ h ∘ g)) ∘ f)
      ↓⟨ ∘-resp-≡ʳ assoc ⟩
        μ.η D ∘ (F₁ (μ.η D) ∘ (F₁ (F₁ h ∘ g) ∘ f))
      ↑⟨ assoc ⟩
        (μ.η D ∘ F₁ (μ.η D)) ∘ (F₁ (F₁ h ∘ g) ∘ f)
      ↓⟨ ∘-resp-≡ˡ M.assoc ⟩
        (μ.η D ∘ μ.η (F₀ D)) ∘ (F₁ (F₁ h ∘ g) ∘ f)
      ↓⟨ assoc ⟩
        μ.η D ∘ (μ.η (F₀ D) ∘ (F₁ (F₁ h ∘ g) ∘ f))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        μ.η D ∘ ((μ.η (F₀ D) ∘ F₁ (F₁ h ∘ g)) ∘ f)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (∘-resp-≡ʳ homomorphism)) ⟩
        μ.η D ∘ ((μ.η (F₀ D) ∘ (F₁ (F₁ h) ∘ F₁ g)) ∘ f)
      ↑⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ assoc) ⟩
        μ.η D ∘ (((μ.η (F₀ D) ∘ F₁ (F₁ h)) ∘ F₁ g) ∘ f)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (∘-resp-≡ˡ (μ.commute h))) ⟩
        μ.η D ∘ (((F₁ h ∘ μ.η C) ∘ F₁ g) ∘ f)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ assoc) ⟩
        μ.η D ∘ ((F₁ h ∘ (μ.η C ∘ F₁ g)) ∘ f)
      ↓⟨ ∘-resp-≡ʳ assoc ⟩
        μ.η D ∘ (F₁ h ∘ ((μ.η C ∘ F₁ g) ∘ f))
      ↑⟨ assoc ⟩
        (μ.η D ∘ F₁ h) ∘ ((μ.η C ∘ F₁ g) ∘ f)
      ∎
    where
    open HomReasoning

  .identityˡ′ : ∀ {A B} {f : A ⇒ F₀ B} → (μ.η B ∘ F₁ (η.η B)) ∘ f ≡ f
  identityˡ′ {A} {B} {f} = 
      begin
        (μ.η B ∘ F₁ (η.η B)) ∘ f
      ↓⟨ ∘-resp-≡ˡ M.identityˡ ⟩
        id ∘ f
      ↓⟨ identityˡ ⟩
        f
      ∎
    where
    open HomReasoning

  .identityʳ′ : ∀ {A B} {f : A ⇒ F₀ B} → (μ.η B ∘ F₁ f) ∘ η.η A ≡ f
  identityʳ′ {A} {B} {f} = 
      begin
        (μ.η B ∘ F₁ f) ∘ η.η A
      ↓⟨ assoc ⟩
        μ.η B ∘ (F₁ f ∘ η.η A)
      ↑⟨ ∘-resp-≡ʳ (η.commute f) ⟩
        μ.η B ∘ (η.η (F₀ B) ∘ f)
      ↑⟨ assoc ⟩
        (μ.η B ∘ η.η (F₀ B)) ∘ f
      ↓⟨ ∘-resp-≡ˡ M.identityʳ ⟩
        id ∘ f
      ↓⟨ identityˡ ⟩
        f
      ∎
    where
    open HomReasoning
