{-# OPTIONS --universe-polymorphism #-}
module Categories.Yoneda where

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.NaturalTransformation using () renaming (promote to promoteNT)
open import Categories.Presheaves

Embed : ∀ {o a} → (C : Category o a) → Functor C (Presheaves C)
Embed C = record
  { F₀ = λ x → Hom[ C ][-, x ]
  ; F₁ = λ {A B} → F₁ {A} {B}
  ; identity = promoteNT (F₁ id) idᴾ (≣-ext (λ _ → identityˡ))
  ; homomorphism = λ {_ _ _ f g} → promoteNT (F₁ (g ∘ f)) (F₁ g ∘ᴾ F₁ f) (≣-ext (λ _ → assoc))
  }
  where
  open Category C
  open Category (Presheaves C) using () renaming (_∘_ to _∘ᴾ_; id to idᴾ)
  open Equiv

  .commute′ : {A B X Y : Obj} (f : A ⇒ B) (g : Y ⇒ X) (x : X ⇒ A) → f ∘ id ∘ x ∘ g ≡ id ∘ (f ∘ x) ∘ g
  commute′ f g x = 
    begin
      f ∘ id ∘ x ∘ g
    ↑⟨ assoc ⟩
      (f ∘ id) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ˡ id-comm ⟩
      (id ∘ f) ∘ x ∘ g
    ≈⟨ assoc ⟩
      id ∘ f ∘ x ∘ g
    ↑⟨ ∘-resp-≡ʳ assoc ⟩
      id ∘ (f ∘ x) ∘ g
    ∎
    where open HomReasoning

  F₁ = λ {A B} f → record
    { η = λ X g → f ∘ g
    ; commute = λ g → ≣-ext (commute′ f g)
    }

