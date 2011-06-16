{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Coproduct {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

-- Borrowed from Dan Doel's definition of coproducts
record Coproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A+B : Obj
    i₁ : A ⇒ A+B
    i₂ : B ⇒ A+B
    [_,_] : ∀ {C} → (A ⇒ C) → (B ⇒ C) → (A+B ⇒ C)

    .commute₁ : ∀ {C} (f : A ⇒ C) (g : B ⇒ C) → [ f , g ] ∘ i₁ ≡ f
    .commute₂ : ∀ {C} (f : A ⇒ C) (g : B ⇒ C) → [ f , g ] ∘ i₂ ≡ g
    .universal : ∀ {C} (f : A ⇒ C) (g : B ⇒ C) (h : A+B ⇒ C)
               → [ f , g ] ∘ i₁ ≡ f
               → [ f , g ] ∘ i₂ ≡ g
               → [ f , g ] ≡ h

  .η : [ i₁ , i₂ ] ≡ id
  η = universal i₁ i₂ id (commute₁ i₁ i₂) (commute₂ i₁ i₂)

record BinaryCoproducts : Set (o ⊔ ℓ ⊔ e) where
  field
    coproduct : ∀ {A B} → Coproduct A B

  _+_ : Obj → Obj → Obj
  A + B = Coproduct.A+B (coproduct {A} {B})