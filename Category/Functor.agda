{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Functor where

record Functor {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Category.Category C renaming (Obj to ObjC; Hom to HomC; id to idC; _∘_ to _∘C_; _≡_ to _≡C_)
  open Category.Category D renaming (Obj to ObjD; Hom to HomD; id to idD; _∘_ to _∘D_; _≡_ to _≡D_)

  field
    F₀ : ObjC → ObjD
    F₁ : ∀ {A B} → HomC A B → HomD (F₀ A) (F₀ B)

    .identity : ∀ {A} → F₁ (idC {A}) ≡D idD
    .homomorphism : ∀ {A B C} {f : HomC A B} {g : HomC B C}
                  → F₁ (g ∘C f) ≡D F₁ g ∘D F₁ f
    .F-resp-≡ : ∀ {A B} {F G : HomC A B} → F ≡C G → F₁ F ≡D F₁ G


Endofunctor : ∀ {o ℓ e} → Category o ℓ e → Set _
Endofunctor C = Functor C C

id : ∀ {o ℓ e} {C : Category o ℓ e} → Endofunctor C
id {C = C} = record 
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = IsEquivalence.refl (Category.equiv C)
  ; homomorphism = IsEquivalence.refl (Category.equiv C)
  ; F-resp-≡ = λ x → x
  }

_∘_ : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′} 
    → Functor D E → Functor C D → Functor C E
_∘_ {C = C} {D = D} {E = E} F G = record 
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≡ = ∘-resp-≡′
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  module E = Category.Category E
  open C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
  open D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
  open E renaming (_∘_ to _∘E_; _≡_ to _≡E_)
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)

  .identity′ : ∀ {A} → F₁ (G₁ (C.id {A})) ≡E E.id
  identity′ = begin
                F₁ (G₁ C.id)
              ≈⟨ F-resp-≡ G.identity ⟩
                F₁ D.id
              ≈⟨ F.identity ⟩
                E.id
              ∎
    where
    open SetoidReasoning E.hom-setoid

  .homomorphism′ : ∀ {X Y Z} {f : C.Hom X Y} {g : C.Hom Y Z}
                 → F₁ (G₁ (g ∘C f)) ≡E F₁ (G₁ g) ∘E F₁ (G₁ f)
  homomorphism′ {f = f} {g = g} = begin
                                    F₁ (G₁ (g ∘C f))
                                  ≈⟨ F-resp-≡ G.homomorphism ⟩
                                    F₁ ((G₁ g) ∘D (G₁ f))
                                  ≈⟨ F.homomorphism ⟩
                                    (F₁ (G₁ g) ∘E F₁ (G₁ f))
                                  ∎
    where
    open SetoidReasoning E.hom-setoid

  .∘-resp-≡′ : ∀ {A B} {F G : C.Hom A B} 
            → F ≡C G → F₁ (G₁ F) ≡E F₁ (G₁ G)
  ∘-resp-≡′ = λ x → F-resp-≡ (G-resp-≡ x)
