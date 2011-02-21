{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Pullback {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

record Pullback {X Y Z}(f : Hom X Z)(g : Hom Y Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    P  : Obj
    p₁ : Hom P X
    p₂ : Hom P Y

  field
    .commutes : f ∘ p₁ ≡ g ∘ p₂

    -- FIXME: this should be irrelevant, right? Agda won't let it be, though.
    universal : ∀ {Q}(q₁ : Hom Q X)(q₂ : Hom Q Y)
              → (commutes : f ∘ q₁ ≡ g ∘ q₂) → Hom Q P

    .universal-unique : ∀ {Q} {q₁ : Hom Q X} {q₂ : Hom Q Y}
                        {commutes : f ∘ q₁ ≡ g ∘ q₂}
                          (u : Hom Q P)
                          (p₁∘u≡q₁ : p₁ ∘ u ≡ q₁)
                          (p₂∘u≡q₂ : p₂ ∘ u ≡ q₂)
                      →   u ≡ universal q₁ q₂ commutes

    .p₁∘universal≡q₁  : ∀ {Q} {q₁ : Hom Q X} {q₂ : Hom Q Y}
                          {commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₁ ∘ universal q₁ q₂ commutes ≡ q₁)

    .p₂∘universal≡q₂  : ∀ {Q} {q₁ : Hom Q X} {q₂ : Hom Q Y}
                          {commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₂ ∘ universal q₁ q₂ commutes ≡ q₂)


