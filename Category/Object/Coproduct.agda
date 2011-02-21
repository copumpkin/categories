{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Object.Coproduct {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

-- Borrowed from Dan Doel's definition of coproducts
record Coproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A+B : Obj
    i₁ : Hom A A+B
    i₂ : Hom B A+B
    [_,_] : ∀ {C} → Hom A C → Hom B C → Hom A+B C

    .commute₁ : ∀ {C} (f : Hom A C) (g : Hom B C) → [ f , g ] ∘ i₁ ≡ f
    .commute₂ : ∀ {C} (f : Hom A C) (g : Hom B C) → [ f , g ] ∘ i₂ ≡ g
    .universal : ∀ {C} (f : Hom A C) (g : Hom B C) (h : Hom A+B C)
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