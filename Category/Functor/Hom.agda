{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Hom where

open import Support
open import Category
open import Category.Bifunctor using (Bifunctor)
open import Category.Agda

Hom : ∀ {o ℓ e} → {C : Category o ℓ e} → Bifunctor (Category.op C) C (Setoids ℓ e)
Hom {_} {ℓ} {e} {C = C} = record
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
    { Carrier = Category.Hom C (fst x) (snd x)
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }

  .cong′ : ∀ {A B} → (f : Category.Hom C (fst B) (fst A) × Category.Hom C (snd A) (snd B)) 
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
                → {f : Category.Hom C (fst Y) (fst X) × Category.Hom C (snd X) (snd Y)}
                → {g : Category.Hom C (fst Z) (fst Y) × Category.Hom C (snd Y) (snd Z)}
                → {x : Category.Hom C (fst X) (snd X)}
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

  .F-resp-≡′ : {A B : Obj × Obj} {F G : Category.Hom C (fst B) (fst A) × Category.Hom C (snd A) (snd B)}
           → fst F ≡ fst G × snd F ≡ snd G
           → {x : Category.Hom C (fst A) (snd A)}
           → snd F ∘ x ∘ fst F ≡ snd G ∘ x ∘ fst G
  F-resp-≡′ (fstF≡fstG , sndF≡sndG) = ∘-resp-≡ sndF≡sndG (∘-resp-≡ʳ fstF≡fstG)
