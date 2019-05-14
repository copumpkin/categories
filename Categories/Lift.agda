{-# OPTIONS --universe-polymorphism #-}
module Categories.Lift where

open import Level
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor; module Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation)

private
  Lifted₂ : ∀ ℓ {a} {a′} {A : Set a} {b} → (A → A → Set b) → (Lift {a} a′ A) → (Lift {a} a′ A) → Set (b ⊔ ℓ)
  Lifted₂ ℓ f x y = Lift  ℓ  (f (lower x) (lower y))

  lifted₂ : ∀ {a a′ b b′} {A A′ : Set a} {B : Set b} → (A → A′ → B) → Lift  a′ A → Lift  a′ A′ → Lift  b′ B
  lifted₂ f x y = lift (f (lower x) (lower y))

LiftC : ∀ {o ℓ e} o′ ℓ′ e′ → Category o ℓ e → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
LiftC o′ ℓ′ e′ C =
  record
  { Obj = Lift  o′ Obj
  ; _⇒_ = Lifted₂ ℓ′ _⇒_
  ; _≡_ = Lifted₂ e′ _≡_
  ; id = lift id
  ; _∘_ = lifted₂ _∘_
  ; assoc = lift assoc
  ; identityˡ = lift identityˡ
  ; identityʳ = lift identityʳ
  ; equiv = record { refl = lift Equiv.refl
                   ; sym = lift ∙ Equiv.sym ∙ lower
                   ; trans = lifted₂ Equiv.trans
                   }
  ; ∘-resp-≡ = lifted₂ ∘-resp-≡
  }
  where open Category C

LiftF : ∀ {oC ℓC eC oD ℓD eD} oC′ ℓC′ eC′ oD′ ℓD′ eD′ {C : Category oC ℓC eC} {D : Category oD ℓD eD} → Functor C D → Functor (LiftC oC′ ℓC′ eC′ C) (LiftC oD′ ℓD′ eD′ D)
LiftF _ _ _ _ _ _ F =
  record
  { F₀ = lift ∙ F₀ ∙ lower
  ; F₁ = lift ∙ F₁ ∙ lower
  ; identity = lift identity
  ; homomorphism = lift homomorphism
  ; F-resp-≡ = lift ∙ F-resp-≡ ∙ lower
  }
  where open Functor F

LiftFˡ : ∀ {oC ℓC eC oD ℓD eD} {C : Category oC ℓC eC} {D : Category oD ℓD eD} → Functor C D → Functor (LiftC oD ℓD eD C) D
LiftFˡ F = 
  record
  { F₀ = F₀ ∙ lower
  ; F₁ = F₁ ∙ lower
  ; identity = identity
  ; homomorphism = homomorphism
  ; F-resp-≡ = F-resp-≡ ∙ lower
  }
  where open Functor F

LiftFʳ : ∀ {oC ℓC eC oD ℓD eD} {C : Category oC ℓC eC} {D : Category oD ℓD eD} → Functor C D → Functor C (LiftC oC ℓC eC D)
LiftFʳ F = 
  record
  { F₀ = lift ∙ F₀
  ; F₁ = lift ∙ F₁
  ; identity = lift identity
  ; homomorphism = lift homomorphism
  ; F-resp-≡ = lift ∙ F-resp-≡
  }
  where open Functor F

LiftNT : ∀ {oC ℓC eC oD ℓD eD oC′ ℓC′ eC′ oD′ ℓD′ eD′} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {F G : Functor C D} → NaturalTransformation F G → NaturalTransformation (LiftF oC′ ℓC′ eC′ oD′ ℓD′ eD′ F) (LiftF oC′ ℓC′ eC′ oD′ ℓD′ eD′ G)
LiftNT α = record { η = lift ∙ η ∙ lower; commute = lift ∙ commute ∙ lower }
  where open NaturalTransformation α
