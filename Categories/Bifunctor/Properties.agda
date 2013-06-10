module Categories.Bifunctor.Properties where

open import Data.Product
open import Function renaming (_∘_ to _∙_)

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Category
open import Categories.Functor
open import Categories.Bifunctor

Chooseˡ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Category.Obj C → Bifunctor C D E → Functor D E
Chooseˡ {C = C} c F = record
  { F₀ = λ d → F₀ (c , d)
  ; F₁ = λ f → F₁ (idᶜ , f)
  ; identity = identity
  ; homomorphism = ≣-trans
    (≣-cong (let h = _ in λ f → F₁ (f , h)) (≣-sym identityᶜ))
    homomorphism
  }
  where
  open Functor F
  idᶜ = Category.id C {c}

  .identityᶜ : C [ idᶜ ∘ idᶜ ] ≣ idᶜ
  identityᶜ = Category.identityˡ C

Chooseʳ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Category.Obj D → Bifunctor C D E → Functor C E
Chooseʳ {D = D} d F = record
  { F₀ = λ c → F₀ (c , d)
  ; F₁ = λ f → F₁ (f , idᵈ)
  ; identity = identity
  ; homomorphism = ≣-trans
    (≣-cong (F₁ ∙ ,_) (≣-sym identityᵈ))
    homomorphism
  }
  where
  open Functor F
  idᵈ = Category.id D {d}

  .identityᵈ : D [ idᵈ ∘ idᵈ ] ≣ idᵈ
  identityᵈ = Category.identityˡ D
