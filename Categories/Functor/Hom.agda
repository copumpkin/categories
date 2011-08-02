{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Hom where

open import Data.Product using (_×_; uncurry; proj₁; proj₂; _,_)

open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions renaming (id to id′)
open import Categories.Category
open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.Agda

module Hom {o ℓ e} (C : Category o ℓ e) where
  open Category C

  Hom[-,-] : Bifunctor (Category.op C) C (ISetoids ℓ e)
  Hom[-,-] = record
    { F₀ = F₀′
    ; F₁ = λ f → record
      { _⟨$⟩_ = λ x → proj₂ f ∘ x ∘ proj₁ f
      ; cong = cong′ f
      }
    ; identity = identity′
    ; homomorphism = homomorphism′
    ; F-resp-≡ = F-resp-≡′
    }
    where

    F₀′ : Obj × Obj → Setoid ℓ e
    F₀′ x = record
      { Carrier = uncurry _⇒_ x
      ; _≈_ = _≡_
      ; isEquivalence = equiv
      }

    _⇆_ : ∀ A B → Set ℓ
    A ⇆ B = (proj₁ B ⇒ proj₁ A) × (proj₂ A ⇒ proj₂ B)

    .cong′ : ∀ {A B} → (f : A ⇆ B) → {x y : uncurry _⇒_ A} → x ≡ y
           → proj₂ f ∘ x ∘ proj₁ f ≡ proj₂ f ∘ y ∘ proj₁ f
    cong′ f x≡y = ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y)

    .identity′ : {A : Obj × Obj} {x y : uncurry _⇒_ A} → x ≡ y → id ∘ x ∘ id ≡ y
    identity′ {A} {x} {y} x≡y =
      begin
        id ∘ x ∘ id
      ↓⟨ identityˡ ⟩
        x ∘ id
      ↓⟨ identityʳ ⟩
        x
      ↓⟨ x≡y ⟩
        y
      ∎
      where
      open HomReasoning
  
    .homomorphism′ : {X Y Z : Obj × Obj}
                   → {f : X ⇆ Y}
                   → {g : Y ⇆ Z}
                   → {x y : uncurry _⇒_ X} → (x ≡ y)
                   → (proj₂ g ∘ proj₂ f) ∘ (x ∘ (proj₁ f ∘ proj₁ g)) ≡ proj₂ g ∘ ((proj₂ f ∘ (y ∘ proj₁ f)) ∘ proj₁ g)
    homomorphism′ {f = f} {g} {x} {y} x≡y =
      begin
        (proj₂ g ∘ proj₂ f) ∘ (x ∘ (proj₁ f ∘ proj₁ g))
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y) ⟩
        (proj₂ g ∘ proj₂ f) ∘ (y ∘ (proj₁ f ∘ proj₁ g))
      ↓⟨ assoc ⟩
        proj₂ g ∘ (proj₂ f ∘ (y ∘ (proj₁ f ∘ proj₁ g)))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        proj₂ g ∘ ((proj₂ f ∘ y) ∘ (proj₁ f ∘ proj₁ g))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        proj₂ g ∘ (((proj₂ f ∘ y) ∘ proj₁ f) ∘ proj₁ g)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ assoc) ⟩
        proj₂ g ∘ ((proj₂ f ∘ (y ∘ proj₁ f)) ∘ proj₁ g)
      ∎
      where
      open HomReasoning

    .F-resp-≡′ : {A B : Obj × Obj} {f g : A ⇆ B}
               → proj₁ f ≡ proj₁ g × proj₂ f ≡ proj₂ g
               → {x y : uncurry _⇒_ A} → (x ≡ y)
               → proj₂ f ∘ x ∘ proj₁ f ≡ proj₂ g ∘ y ∘ proj₁ g
    F-resp-≡′ (f₁≡g₁ , f₂≡g₂) x≡y = ∘-resp-≡ f₂≡g₂ (∘-resp-≡ x≡y f₁≡g₁)

  Hom[_,-] : Obj → Functor C (ISetoids ℓ e)
  Hom[_,-] B = record
    { F₀ = λ x → Hom[-,-].F₀ (B , x)
    ; F₁ = λ f → Hom[-,-].F₁ (id , f)
    ; identity = Hom[-,-].identity
    ; homomorphism = homomorphism′
    ; F-resp-≡ = λ F≡G x≡y → ∘-resp-≡ F≡G (∘-resp-≡ˡ x≡y)
    }
    where
    module Hom[-,-] = Functor Hom[-,-]

    -- I can't see an easy way to reuse the proof for the bifunctor :(
    -- luckily, it's an easy proof!
    .homomorphism′ : {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} {x y : B ⇒ X}
                   → (x ≡ y)   → (g ∘ f) ∘ (x ∘ id) ≡ g ∘ ((f ∘ (y ∘ id)) ∘ id)
    homomorphism′ {f = f} {g} {x} {y} x≡y =
      begin
        (g ∘ f) ∘ (x ∘ id)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y) ⟩
        (g ∘ f) ∘ (y ∘ id)
      ↓⟨ assoc ⟩
        g ∘ (f ∘ (y ∘ id))
      ↑⟨ ∘-resp-≡ʳ identityʳ ⟩
        g ∘ ((f ∘ (y ∘ id)) ∘ id)
      ∎
      where
      open HomReasoning

  Hom[-,_] : Obj → Functor (Category.op C) (ISetoids ℓ e)
  Hom[-,_] B = record
    { F₀ = λ x → Hom[-,-].F₀ (x , B)
    ; F₁ = λ f → Hom[-,-].F₁ (f , id)
    ; identity = Hom[-,-].identity
    ; homomorphism = homomorphism′
    ; F-resp-≡ = λ F≡G x≡y → ∘-resp-≡ʳ (∘-resp-≡ x≡y F≡G)
    }
    where
    module Hom[-,-] = Functor Hom[-,-]

    .homomorphism′ : {X Y Z : Obj} {f : Y ⇒ X} {g : Z ⇒ Y} {x y : X ⇒ B} →
                    (x ≡ y) → id ∘ (x ∘ (f ∘ g)) ≡ id ∘ ((id ∘ (y ∘ f)) ∘ g)
    homomorphism′ {f = f} {g} {x} {y} x≡y =
      begin
        id ∘ (x ∘ (f ∘ g))
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y) ⟩
        id ∘ (y ∘ (f ∘ g))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        id ∘ ((y ∘ f) ∘ g)
      ↑⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ identityˡ) ⟩
        id ∘ ((id ∘ (y ∘ f)) ∘ g)
      ∎
      where
      open HomReasoning

-- More explicit versions

Hom[_][-,-] : ∀ {o ℓ e} → (C : Category o ℓ e) → Bifunctor (Category.op C) C (ISetoids ℓ e)
Hom[ C ][-,-] = Hom[-,-]
  where open Hom C

Hom[_][_,-] : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Functor C (ISetoids ℓ e)
Hom[ C ][ B ,-] = Hom[ B ,-]
  where open Hom C

Hom[_][-,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Functor (Category.op C) (ISetoids ℓ e)
Hom[ C ][-, B ] = Hom[-, B ]
  where open Hom C