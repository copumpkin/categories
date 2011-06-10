{-# OPTIONS --universe-polymorphism #-}

open import Support hiding (⊤)
open import Category

module Category.Object.Terminal {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

record Terminal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤ : Obj
    ! : ∀ {A} → (A ⇒ ⊤)
    !-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≡ f

  .!-unique₂ : ∀ {A} → (f g : A ⇒ ⊤) → f ≡ g
  !-unique₂ f g =
    begin
      f
    ↑⟨ !-unique f ⟩
      !
    ↓⟨ !-unique g ⟩
      g
    ∎
    where open HomReasoning

  .⊤-id : (f : ⊤ ⇒ ⊤) → f ≡ id
  ⊤-id f = !-unique₂ f id
  