{-# OPTIONS --universe-polymorphism #-}
module Categories.Lift where

open import Level
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Support.PropositionalEquality

open import Categories.Category using (Category; module Category; EasyCategory; EASY_)
open import Categories.Functor using (Functor; module Functor; module EasyFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation)

private
  Lifted₂ : ∀ ℓ {a} {a′} {A : Set a} {b} → (A → A → Set b) → (Lift {a} {a′} A) → (Lift {a} {a′} A) → Set (b ⊔ ℓ)
  Lifted₂ ℓ f x y = Lift {ℓ = ℓ} (f (lower x) (lower y))

  lifted₂ : ∀ {a a′ b b′} {A A′ : Set a} {B : Set b} → (A → A′ → B) → Lift {ℓ = a′} A → Lift {ℓ = a′} A′ → Lift {ℓ = b′} B
  lifted₂ f x y = lift (f (lower x) (lower y))

LiftCᵉ : ∀ {o a} o′ a′ → Category o a → EasyCategory (o ⊔ o′) (a ⊔ a′) (a ⊔ a′)
LiftCᵉ o′ a′ C = record
  { Obj = Lift {ℓ = o′} Obj
  ; _⇒_ = Lifted₂ a′ _⇒_
  ; _≡_ = Lifted₂ a′ _≡_
  ; id = lift id
  ; compose = lifted₂ compose
  ; assoc = lift assoc
  ; identityˡ = lift identityˡ
  ; identityʳ = lift identityʳ
  ; promote = promote′
  ; REFL = lift ≣-refl
  }
  where
  open Category C

  promote′ : ∀ {A B : Lift {ℓ = o′} Obj} (f g : Lifted₂ a′ _⇒_ A B) → (Lifted₂ a′ _≡_ f g) → f ≣ g
  promote′ (lift f) (lift .f) (lift ≣-refl) = ≣-refl

LiftC : ∀ {o a} o′ a′ → Category o a → Category (o ⊔ o′) (a ⊔ a′)
LiftC o′ a′ C = EASY LiftCᵉ o′ a′ C

LiftF : ∀ {oC aC oD aD} oC′ aC′ oD′ aD′ {C : Category oC aC} {D : Category oD aD} → Functor C D → Functor (LiftC oC′ aC′ C) (LiftC oD′ aD′ D)
LiftF _ _ _ _ {C} {D} F = EasyFunctor.functor {C = LiftC _ _ C} {D = LiftCᵉ _ _ D}
  record
  { F₀ = lift ∙ F₀ ∙ lower
  ; F₁ = lift ∙ F₁ ∙ lower
  ; identity = lift identity
  ; homomorphism = lift homomorphism
  }
  where open Functor F

LiftFˡ : ∀ {oC aC oD aD} {C : Category oC aC} {D : Category oD aD} → Functor C D → Functor (LiftC oD aD C) D
LiftFˡ F = 
  record
  { F₀ = F₀ ∙ lower
  ; F₁ = F₁ ∙ lower
  ; identity = identity
  ; homomorphism = homomorphism
  }
  where open Functor F

LiftFʳ : ∀ {oC aC oD aD} {C : Category oC aC} {D : Category oD aD} → Functor C D → Functor C (LiftC oC aC D)
LiftFʳ {C = C} {D} F = EasyFunctor.functor {C = C} {D = LiftCᵉ _ _ D}
  record
  { F₀ = lift ∙ F₀
  ; F₁ = lift ∙ F₁
  ; identity = lift identity
  ; homomorphism = lift homomorphism
  }
  where open Functor F

LiftNT : ∀ {oC aC oD aD oC′ aC′ oD′ aD′} {C : Category oC aC} {D : Category oD aD} {F G : Functor C D} → NaturalTransformation F G → NaturalTransformation (LiftF oC′ aC′ oD′ aD′ F) (LiftF oC′ aC′ oD′ aD′ G)
LiftNT α = record { η = lift ∙ η ∙ lower; commute = ≣-cong lift ∙ commute ∙ lower }
  where open NaturalTransformation α 
