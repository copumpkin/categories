{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal where

open import Support hiding (_×_)
open import Category

open import Category.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Category.NaturalIsomorphism

module MonoidalHelperFunctors {o ℓ e} (C : Category o ℓ e) (⊗ : Bifunctor C C C) (id : Category.Obj C) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ)

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  open import Category.Product

  id⊗x : Endofunctor C
  id⊗x = record 
    { F₀ = λ x → ⊗₀ (id , x)
    ; F₁ = λ f → ⊗₁ (C.id , f)
    ; identity = identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism′ {f = f} {g}
    ; F-resp-≡ = λ {_} {_} {f} {g} → F-resp-≡′ {F = f} {g}
    }
    where
    .homomorphism′ : ∀ {A B C} {f : Hom A B} {g : Hom B C} 
                  → ⊗₁ (C.id , g ∘ f) ≡ ⊗₁ (C.id , g) ∘ ⊗₁ (C.id , f)
    homomorphism′ {f = f} {g} = 
        begin
          ⊗₁ (C.id , g ∘ f)
        ≈⟨ ⊗-resp-≡ (sym C.identityˡ , IsEquivalence.refl C.equiv) ⟩
          ⊗₁ (C.id ∘ C.id , g ∘ f)
        ≈⟨ ⊗.homomorphism ⟩
          ⊗₁ (C.id , g) ∘ ⊗₁ (C.id , f)
        ∎
      where
      open IsEquivalence C.equiv hiding (refl)
      open SetoidReasoning hom-setoid
    .F-resp-≡′ : ∀ {A B} → {F G : Hom A B} → F ≡ G → ⊗₁ (C.id , F) ≡ ⊗₁ (C.id , G)
    F-resp-≡′ {F = F} {G} F≡G = 
        begin 
          ⊗₁ (C.id , F)
        ≈⟨ ⊗-resp-≡ ((C-refl , F≡G)) ⟩
          ⊗₁ (C.id , G)
        ∎
      where
      open IsEquivalence C.equiv renaming (refl to C-refl)
      open SetoidReasoning hom-setoid

  x⊗id : Endofunctor C
  x⊗id = record 
    { F₀ = λ x → ⊗₀ (x , id)
    ; F₁ = λ f → ⊗₁ (f , C.id)
    ; identity = identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism′ {f = f} {g}
    ; F-resp-≡ = λ {_} {_} {f} {g} → F-resp-≡′ {F = f} {g}
    }
    where
    .homomorphism′ : ∀ {A B C} {f : Hom A B} {g : Hom B C} 
                  → ⊗₁ (g ∘ f , C.id) ≡ ⊗₁ (g , C.id) ∘ ⊗₁ (f , C.id)
    homomorphism′ {f = f} {g} = 
        begin
          ⊗₁ (g ∘ f , C.id)
        ≈⟨ ⊗-resp-≡ (IsEquivalence.refl C.equiv , sym C.identityˡ) ⟩
          ⊗₁ (g ∘ f , C.id ∘ C.id)
        ≈⟨ ⊗.homomorphism ⟩
          ⊗₁ (g , C.id) ∘ ⊗₁ (f , C.id)
        ∎
      where
      open IsEquivalence C.equiv hiding (refl)
      open SetoidReasoning hom-setoid
    .F-resp-≡′ : ∀ {A B} → {F G : Hom A B} → F ≡ G → ⊗₁ (F , C.id) ≡ ⊗₁ (G , C.id)
    F-resp-≡′ {F = F} {G} F≡G = 
        begin 
          ⊗₁ (F , C.id)
        ≈⟨ ⊗-resp-≡ (F≡G , C-refl) ⟩
          ⊗₁ (G , C.id)
        ∎
      where
      open IsEquivalence C.equiv renaming (refl to C-refl)
      open SetoidReasoning hom-setoid

  Triendo : Set (o ⊔ ℓ ⊔ e)
  Triendo = Functor (Product (Product C C) C) C

  [x⊗y]⊗z : Triendo
  [x⊗y]⊗z = ⊗ ∘F (⊗ ⁂ idF {C = C})

  x⊗[y⊗z] : Triendo 
  x⊗[y⊗z] = (⊗ ∘F (idF {C = C} ⁂ ⊗)) ∘F preassoc C C C

record Monoidal {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category.Category C
  open C hiding (id; identityˡ; identityʳ; assoc)

  field
    ⊗  : Bifunctor C C C
    id : Obj

  private module ⊗ = Functor ⊗ renaming (F₀ to ⊗₀; F₁ to ⊗₁; F-resp-≡ to ⊗-resp-≡)
  open ⊗

  open MonoidalHelperFunctors C ⊗ id

  field
    identityˡ : NaturalIsomorphism id⊗x idF
    identityʳ : NaturalIsomorphism x⊗id idF
    assoc : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]