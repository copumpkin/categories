{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Initial {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

record Initial : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊥ : Obj
    ! : ∀ {A} → (⊥ ⇒ A)
    .!-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! ≡ f

  .!-unique₂ : ∀ {A} → (f g : ⊥ ⇒ A) → f ≡ g
  !-unique₂ f g =
      begin
        f
      ↑⟨ !-unique f ⟩
        !
      ↓⟨ !-unique g ⟩
        g
      ∎
    where
    open HomReasoning

  .⊥-id : (f : ⊥ ⇒ ⊥) → f ≡ id
  ⊥-id f = !-unique₂ f id

import Categories.Morphisms
open Categories.Morphisms C
open Initial

.to-⊥-is-Epi : ∀ {A : Obj} {i : Initial} → (f : A ⇒ ⊥ i) → Epi f
to-⊥-is-Epi {_} {i} f = helper
  where
    helper : ∀ {C : Obj} → (g h : ⊥ i ⇒ C) → g ∘ f ≡ h ∘ f → g ≡ h
    helper g h _ = !-unique₂ i g h

