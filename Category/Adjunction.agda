{-# OPTIONS --universe-polymorphism #-}
module Category.Adjunction where

open import Support
open import Category
open import Category.Functor renaming (id to idF; _≡_ to _≡F_)
open import Category.NaturalTransformation
open import Category.Monad

record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} (F : Functor D C) (G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  field
    unit   : NaturalTransformation idF (G ∘ F)
    counit : NaturalTransformation (F ∘ G) idF

    .zig : id ≡ (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : id ≡ (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

  private module C = Category.Category C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
  private module D = Category.Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
  open C
  open D

  private module F = Functor F
  private module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open F
  open G

  private module unit   = NaturalTransformation unit
  private module counit = NaturalTransformation counit


  monad : Monad D
  monad = record 
    { F = G ∘ F
    ; η = unit
    ; μ = G ∘ˡ (counit ∘ʳ F)
    ; assoc = assoc′
    ; identityˡ = identityˡ′
    ; identityʳ = identityʳ′
    }
    where

    .assoc′ : ∀ {x} 
           → G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (G₁ (counit.η (F₀ x)))) ≡D G₁ (counit.η (F₀ x)) ∘D G₁ (counit.η (F₀ (G₀ (F₀ x))))
    assoc′ {x} = 
        begin
          G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (G₁ (counit.η (F₀ x))))
        ≈⟨ sym G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) ∘C (F₁ (G₁ (counit.η (F₀ x)))))
        ≈⟨ G-resp-≡ (NaturalTransformation.commute counit (counit.η (F₀ x))) ⟩
          G₁ (counit.η (F₀ x) ∘C counit.η (F₀ (G₀ (F₀ x))))
        ≈⟨ G.homomorphism ⟩
          G₁ (counit.η (F₀ x)) ∘D G₁ (counit.η (F₀ (G₀ (F₀ x))))
        ∎
      where
      open IsEquivalence D.equiv
      open SetoidReasoning D.hom-setoid

    .identityˡ′ : ∀ {x} → G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (unit.η x)) ≡D D.id
    identityˡ′ {x} = 
        begin
          G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (unit.η x))
        ≈⟨ sym G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) ∘C (F₁ (unit.η x)))
        ≈⟨ sym (G-resp-≡ zig) ⟩
          G₁ C.id
        ≈⟨ G.identity ⟩
          D.id
        ∎
      where
      open IsEquivalence D.equiv
      open SetoidReasoning D.hom-setoid

    .identityʳ′ : ∀ {x} → G₁ (counit.η (F₀ x)) ∘D unit.η (G₀ (F₀ x)) ≡D D.id
    identityʳ′ = IsEquivalence.sym D.equiv zag

