{-# OPTIONS --universe-polymorphism #-}
module Categories.Adjunction where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalTransformation
open import Categories.Monad

record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} (F : Functor D C) (G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  field
    unit   : NaturalTransformation idF (G ∘F F)
    counit : NaturalTransformation (F ∘F G) idF

    .zig : id ≡ (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : id ≡ (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

  private module C = Category C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
  private module D = Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
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
    { F = G ∘F F
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
        ↑⟨ G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) ∘C (F₁ (G₁ (counit.η (F₀ x)))))
        ↓⟨ G-resp-≡ (NaturalTransformation.commute counit (counit.η (F₀ x))) ⟩
          G₁ (counit.η (F₀ x) ∘C counit.η (F₀ (G₀ (F₀ x))))
        ↓⟨ G.homomorphism ⟩
          G₁ (counit.η (F₀ x)) ∘D G₁ (counit.η (F₀ (G₀ (F₀ x))))
        ∎
      where
      open D.HomReasoning

    .identityˡ′ : ∀ {x} → G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (unit.η x)) ≡D D.id
    identityˡ′ {x} = 
        begin
          G₁ (counit.η (F₀ x)) ∘D G₁ (F₁ (unit.η x))
        ↑⟨ G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) ∘C (F₁ (unit.η x)))
        ↑⟨ G-resp-≡ zig ⟩
          G₁ C.id
        ↓⟨ G.identity ⟩
          D.id
        ∎
      where
      open D.HomReasoning

    .identityʳ′ : ∀ {x} → G₁ (counit.η (F₀ x)) ∘D unit.η (G₀ (F₀ x)) ≡D D.id
    identityʳ′ = D.Equiv.sym zag


{-
_∘_ : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂} 
      {F : Functor D C} {G : Functor C D} {H : Functor E D} {I : Functor D E} → 
      Adjunction F G → Adjunction H I → Adjunction (F ∘F H) (I ∘F G)
_∘_ X Y = record 
  { unit = {!!} ∘₀ {!!}
  ; counit = {!!}
  ; zig = {!!}
  ; zag = {!!}
  }
-}