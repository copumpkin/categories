module Categories.Bifunctor.Properties where

open import Data.Product
open import Function renaming (_∘_ to _∙_)

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Category
open import Categories.Functor
open import Categories.FunctorCategory
open import Categories.Bifunctor
open import Categories.NaturalTransformation as NT
open import Categories.Square

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

Curryˡ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Bifunctor C D E → Functor C (Functors D E)
Curryˡ {C = C} {D} {E} F = record
  { F₀ = flip (Chooseˡ {C = C}) F
  ; F₁ = Curryˡ₁
  ; identity = NT.promote (Curryˡ₁ C.id) NT.id F.identity
  ; homomorphism = λ {X Y Z f g} → NT.promote (Curryˡ₁ (g ∘ f)) (Curryˡ₁ g ∘₁ Curryˡ₁ f) (≣-trans (≣-cong (λ h → F₁ (g ∘ f , h)) (≣-sym D.identityˡ)) F.homomorphism)
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  open C
  open D
  open E
  module F = Functor F
  open F

  Curryˡ₁ : ∀ {A B} (f : C [ A , B ]) → Functors D E [ Chooseˡ {C = C} A F , Chooseˡ {C = C} B F ]
  Curryˡ₁ f = record
    { η = λ X → F₁ (f , D.id)
    ; commute = λ g → let open E.HomReasoning in
      begin
        F₁ (f , D.id) ∘ F₁ (C.id , g)
      ↑⟨ F.homomorphism ⟩
        F₁ (f ∘ C.id , D.id ∘ g)
      ↓⟨ ≣-cong₂ (curry F₁) C.id-comm (≣-sym D.id-comm) ⟩
        F₁ (C.id ∘ f , g ∘ D.id)
      ↓⟨ F.homomorphism ⟩
        F₁ (C.id , g) ∘ F₁ (f , D.id)
      ∎
    }

Uncurryˡ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Functor C (Functors D E) → Bifunctor C D E
Uncurryˡ {C = C} {D} {E} F = record
  { F₀ = uncurry′ (map₀ ∙ F₀)
  ; F₁ = uncurry′ (λ x y → η (F₁ x) _ ∘ map₁ (F₀ _) y)
  ; identity = let open E.HomReasoning in begin
        (η (F₁ C.id) _) ∘ map₁ (F₀ _) D.id
      ↓⟨ ≣-app (≣-cong η F.identity) _ ⟩∘⟨ Functor.identity (F₀ _) ⟩
        E.id ∘ E.id
      ↓⟨ E.identityˡ ⟩
        E.id
      ∎
  ; homomorphism = λ {X Y Z f g} → let open E.HomReasoning in
                                   let open GlueSquares E in
                                   let f₁ , f₂ = f in
                                   let g₁ , g₂ = g in
      begin
        η (F₁ (g₁ ∘ f₁)) _ ∘ map₁ (F₀ _) (g₂ ∘ f₂)
      ↓⟨ (≣-app (≣-cong η F.homomorphism) _) ⟩∘⟨ Functor.homomorphism (F₀ _) ⟩
        (η (F₁ g₁) _ ∘ η (F₁ f₁) _) ∘ map₁ (F₀ _) g₂ ∘ map₁ (F₀ _) f₂
      ↓⟨ extend² (commute (F₁ f₁) g₂) ⟩
        (η (F₁ g₁) _ ∘ map₁ (F₀ _) g₂) ∘ (η (F₁ f₁) _ ∘ map₁ (F₀ _) f₂)
      ∎
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  open C
  open D
  open E
  module F = Functor F
  open F
  open Functor renaming (F₀ to map₀; F₁ to map₁)
  open NaturalTransformation

Curryʳ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Bifunctor C D E → Functor D (Functors C E)
Curryʳ {C = C} {D} {E} F = Curryˡ (flip-bifunctor {C = C} {D} F)

Uncurryʳ : ∀ {o a} {o′ a′} {o″ a″} {C : Category o a} {D : Category o′ a′} {E : Category o″ a″} → Functor C (Functors D E) → Bifunctor D C E
Uncurryʳ {C = C} {D} {E} F = flip-bifunctor {C = C} {D} (Uncurryˡ F)
