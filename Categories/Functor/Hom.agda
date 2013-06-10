{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Hom where

open import Data.Product using (_×_; uncurry; proj₁; proj₂; _,_)

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Category
open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.Agda

module Hom {o a} (C : Category o a) where
  open Category C

  Hom[-,-] : Bifunctor (Category.op C) C (Sets a)
  Hom[-,-] = record
    { F₀ = F₀′
    ; F₁ = λ f x → proj₂ f ∘ x ∘ proj₁ f
    ; identity = ≣-ext identity′
    ; homomorphism = ≣-ext homomorphism′
    }
    where

    F₀′ : Obj × Obj → Set a
    F₀′ x = uncurry _⇒_ x

    _⇆_ : ∀ A B → Set a
    A ⇆ B = (proj₁ B ⇒ proj₁ A) × (proj₂ A ⇒ proj₂ B)

    .cong′ : ∀ {A B} → (f : A ⇆ B) → {x y : uncurry _⇒_ A} → x ≡ y
           → proj₂ f ∘ x ∘ proj₁ f ≡ proj₂ f ∘ y ∘ proj₁ f
    cong′ f x≡y = ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y)

    .identity′ : {A : Obj × Obj} (x : uncurry _⇒_ A) → id ∘ x ∘ id ≡ x
    identity′ {A} x =
      begin
        id ∘ x ∘ id
      ↓⟨ identityˡ ⟩
        x ∘ id
      ↓⟨ identityʳ ⟩
        x
      ∎
      where
      open HomReasoning
  
    .homomorphism′ : {X Y Z : Obj × Obj}
                   → {f : X ⇆ Y}
                   → {g : Y ⇆ Z}
                   → (x : uncurry _⇒_ X)
                   → (proj₂ g ∘ proj₂ f) ∘ (x ∘ (proj₁ f ∘ proj₁ g)) ≡ proj₂ g ∘ ((proj₂ f ∘ (x ∘ proj₁ f)) ∘ proj₁ g)
    homomorphism′ {f = f} {g} x =
      begin
        (proj₂ g ∘ proj₂ f) ∘ (x ∘ (proj₁ f ∘ proj₁ g))
      ↓⟨ assoc ⟩
        proj₂ g ∘ (proj₂ f ∘ (x ∘ (proj₁ f ∘ proj₁ g)))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        proj₂ g ∘ ((proj₂ f ∘ x) ∘ (proj₁ f ∘ proj₁ g))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        proj₂ g ∘ (((proj₂ f ∘ x) ∘ proj₁ f) ∘ proj₁ g)
      ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ assoc) ⟩
        proj₂ g ∘ ((proj₂ f ∘ (x ∘ proj₁ f)) ∘ proj₁ g)
      ∎
      where
      open HomReasoning

  Hom[_,-] : Obj → Functor C (Sets a)
  Hom[_,-] B = record
    { F₀ = λ x → Hom[-,-].F₀ (B , x)
    ; F₁ = λ f → Hom[-,-].F₁ (id , f)
    ; identity = Hom[-,-].identity
    ; homomorphism = ≣-ext homomorphism′
    }
    where
    module Hom[-,-] = Functor Hom[-,-]

    -- I can't see an easy way to reuse the proof for the bifunctor :(
    -- luckily, it's an easy proof!
    .homomorphism′ : {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z}
                   → (x : B ⇒ X)
                   → (g ∘ f) ∘ (x ∘ id) ≡ g ∘ ((f ∘ (x ∘ id)) ∘ id)
    homomorphism′ {f = f} {g} x =
      begin
        (g ∘ f) ∘ (x ∘ id)
      ↓⟨ assoc ⟩
        g ∘ (f ∘ (x ∘ id))
      ↑⟨ ∘-resp-≡ʳ identityʳ ⟩
        g ∘ ((f ∘ (x ∘ id)) ∘ id)
      ∎
      where
      open HomReasoning

  Hom[-,_] : Obj → Functor (Category.op C) (Sets a)
  Hom[-,_] B = record
    { F₀ = λ x → Hom[-,-].F₀ (x , B)
    ; F₁ = λ f → Hom[-,-].F₁ (f , id)
    ; identity = Hom[-,-].identity
    ; homomorphism = ≣-ext homomorphism′
    }
    where
    module Hom[-,-] = Functor Hom[-,-]

    .homomorphism′ : {X Y Z : Obj} {f : Y ⇒ X} {g : Z ⇒ Y}
                   → (x : X ⇒ B)
                   → id ∘ (x ∘ (f ∘ g)) ≡ id ∘ ((id ∘ (x ∘ f)) ∘ g)
    homomorphism′ {f = f} {g} x =
      begin
        id ∘ (x ∘ (f ∘ g))
      ↑⟨ ∘-resp-≡ʳ assoc ⟩
        id ∘ ((x ∘ f) ∘ g)
      ↑⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ identityˡ) ⟩
        id ∘ ((id ∘ (x ∘ f)) ∘ g)
      ∎
      where
      open HomReasoning

-- More explicit versions

Hom[_][-,-] : ∀ {o a} → (C : Category o a) → Bifunctor (Category.op C) C (Sets a)
Hom[ C ][-,-] = Hom[-,-]
  where open Hom C

Hom[_][_,-] : ∀ {o a} → (C : Category o a) → Category.Obj C → Functor C (Sets a)
Hom[ C ][ B ,-] = Hom[ B ,-]
  where open Hom C

Hom[_][-,_] : ∀ {o a} → (C : Category o a) → Category.Obj C → Functor (Category.op C) (Sets a)
Hom[ C ][-, B ] = Hom[-, B ]
  where open Hom C
