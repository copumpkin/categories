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
