{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal where

open import Support hiding (_×_)
open import Category

open import Category.Bifunctor renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Category.NaturalIsomorphism

{-
module MonoidalHelperFunctors {o ℓ e} (C : Category o ℓ e) (⊗ : Bifunctor C C C) (id : Category.Obj C) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ)

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  id⊗x : Endofunctor C
  id⊗x = record 
    { F₀ = λ x → ⊗₀ (id , x)
    ; F₁ = λ f → ⊗₁ (C.id , f)
    ; identity = identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism′ {f = f} {g}
    ; F-resp-≡ = {!!}
    }
    where
    .homomorphism′ : ∀ {A B C} {f : Hom A B} {g : Hom B C} 
                  → ⊗₁ (C.id , g ∘ f) ≡ ⊗₁ (C.id , g) ∘ ⊗₁ (C.id , f)
    homomorphism′ {f = f} {g} = 
        begin
          ⊗₁ (C.id , g ∘ f)
        ≈⟨ ⊗-resp-≡ {!!} ⟩
          {!!}
        ≈⟨ {!!} ⟩
          ⊗₁ (C.id , g) ∘ ⊗₁ (C.id , f)
        ∎
      where
      open IsEquivalence C.equiv
      open SetoidReasoning hom-setoid

  x⊗id : Endofunctor C
  x⊗id = record 
    { F₀ = λ x → ⊗₀ (x , id)
    ; F₁ = λ f → ⊗₁ (f , C.id)
    ; identity = identity
    ; homomorphism = {!!}
    ; F-resp-≡ = {!!}
    }
-}

{-
record Monoidal {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ)

  field
    ⊗  : Bifunctor C C C
    id : Obj

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  open MonoidalHelperFunctors C ⊗ id

  field
    .identityˡ : NaturalIsomorphism id⊗x idF
    .identityʳ : NaturalIsomorphism x⊗id idF
-}
