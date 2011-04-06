{-# OPTIONS --universe-polymorphism #-}

open import Support hiding (⊤)
open import Category

module Category.Object.Terminal {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

record Terminal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤ : Obj
    ! : ∀ {A} → Hom A ⊤
    !-unique : ∀ {A} → (f : Hom A ⊤) → ! ≡ f

  .⊤-id : (f : Hom ⊤ ⊤) → f ≡ id
  ⊤-id f = 
      begin
        f
      ≈⟨ sym (!-unique f) ⟩
        !
      ≈⟨ !-unique id ⟩
        id
      ∎
    where
    open IsEquivalence equiv
    open SetoidReasoning hom-setoid

  