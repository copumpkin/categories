{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Hom where

open import Support
open import Category
open import Category.Bifunctor using (Bifunctor; Functor; module Functor)
open import Category.Agda

Hom[-,-] : ∀ {o ℓ e} → {C : Category o ℓ e} → Bifunctor (Category.op C) C (Setoids ℓ e)
Hom[-,-] {_} {ℓ} {e} {C = C} = record
  { F₀ = F₀′
  ; F₁ = λ f → record
    { F = λ x → snd f ∘ x ∘ fst f
    ; cong = cong′ f
    }
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≡ = F-resp-≡′
  }
  where
  open Category.Category C

  F₀′ : Obj × Obj → Setoid ℓ e
  F₀′ x = record
    { Carrier = Hom (fst x) (snd x)
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }

  .cong′ : ∀ {A B} → (f : Hom (fst B) (fst A) × Hom (snd A) (snd B)) 
        → {x y : Setoid.Carrier (F₀′ A)} → x ≡ y → snd f ∘ x ∘ fst f ≡ snd f ∘ y ∘ fst f
  cong′ f x≡y = ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y)

  .identity′ : {A : Obj × Obj} → {x : Setoid.Carrier (F₀′ A)} → id ∘ x ∘ id ≡ x
  identity′ {A} {x} =
    begin
      id ∘ x ∘ id
    ≈⟨ identityˡ ⟩
      x ∘ id
    ≈⟨ identityʳ ⟩
      x
    ∎
    where
    open SetoidReasoning hom-setoid

  .homomorphism′ : {X Y Z : Obj × Obj}
                → {f : Hom (fst Y) (fst X) × Hom (snd X) (snd Y)}
                → {g : Hom (fst Z) (fst Y) × Hom (snd Y) (snd Z)}
                → {x : Hom (fst X) (snd X)}
                → (snd g ∘ snd f) ∘ (x ∘ (fst f ∘ fst g)) ≡ snd g ∘ ((snd f ∘ (x ∘ fst f)) ∘ fst g)
  homomorphism′ {f = f} {g} {x} =
    begin
      (snd g ∘ snd f) ∘ (x ∘ (fst f ∘ fst g))
    ≈⟨ assoc ⟩
      snd g ∘ (snd f ∘ (x ∘ (fst f ∘ fst g)))
    ≈⟨ sym (∘-resp-≡ʳ assoc) ⟩
      snd g ∘ ((snd f ∘ x) ∘ (fst f ∘ fst g))
    ≈⟨ sym (∘-resp-≡ʳ assoc) ⟩
      snd g ∘ (((snd f ∘ x) ∘ fst f) ∘ fst g)
    ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ assoc) ⟩
      snd g ∘ ((snd f ∘ (x ∘ fst f)) ∘ fst g)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .F-resp-≡′ : {A B : Obj × Obj} {F G : Hom (fst B) (fst A) × Hom (snd A) (snd B)}
           → fst F ≡ fst G × snd F ≡ snd G
           → {x : Hom (fst A) (snd A)}
           → snd F ∘ x ∘ fst F ≡ snd G ∘ x ∘ fst G
  F-resp-≡′ (fstF≡fstG , sndF≡sndG) = ∘-resp-≡ sndF≡sndG (∘-resp-≡ʳ fstF≡fstG)

Hom[_,-] : ∀ {o ℓ e} → {C : Category o ℓ e} → Category.Obj C → Functor C (Setoids ℓ e)
Hom[_,-] {_} {ℓ} {e} {C} B = record
  { F₀ = λ x → Hom[-,-].F₀ (B , x)
  ; F₁ = λ f → Hom[-,-].F₁ (id , f)
  ; identity = Hom[-,-].identity
  ; homomorphism = homomorphism′
  ; F-resp-≡ = λ F≡G → ∘-resp-≡ˡ F≡G
  }
  where
  open Category.Category C
  module Hom[-,-] = Functor (Hom[-,-] {C = C})

  -- I can't see an easy way to reuse the proof for the bifunctor :(
  -- luckily, it's an easy proof!
  .homomorphism′ : {X Y Z : Obj} {f : Hom X Y} {g : Hom Y Z} {x : Hom B X}
                →  (g ∘ f) ∘ (x ∘ id) ≡ g ∘ ((f ∘ (x ∘ id)) ∘ id)
  homomorphism′ {f = f} {g} {x} =
    begin
      (g ∘ f) ∘ (x ∘ id)
    ≈⟨ assoc ⟩
      g ∘ (f ∘ (x ∘ id))
    ≈⟨ sym (∘-resp-≡ʳ identityʳ) ⟩
      g ∘ ((f ∘ (x ∘ id)) ∘ id)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


Hom[-,_] : ∀ {o ℓ e} → {C : Category o ℓ e} → Category.Obj C → Functor (Category.op C) (Setoids ℓ e)
Hom[-,_] {_} {ℓ} {e} {C} B = record
  { F₀ = λ x → Hom[-,-].F₀ (x , B)
  ; F₁ = λ f → Hom[-,-].F₁ (f , id)
  ; identity = Hom[-,-].identity
  ; homomorphism = homomorphism′
  ; F-resp-≡ = λ F≡G → ∘-resp-≡ʳ (∘-resp-≡ʳ F≡G)
  }
  where
  open Category.Category C
  module Hom[-,-] = Functor (Hom[-,-] {C = C})

  .homomorphism′ : {X Y Z : Obj} {f : Hom Y X} {g : Hom Z Y} {x : Hom X B} →
      id ∘ (x ∘ (f ∘ g)) ≡ id ∘ ((id ∘ (x ∘ f)) ∘ g)
  homomorphism′ {f = f} {g} {x} =
    begin
      id ∘ (x ∘ (f ∘ g))
    ≈⟨ sym (∘-resp-≡ʳ assoc) ⟩
      id ∘ ((x ∘ f) ∘ g)
    ≈⟨ sym (∘-resp-≡ʳ (∘-resp-≡ˡ identityˡ)) ⟩
      id ∘ ((id ∘ (x ∘ f)) ∘ g)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv
