{-# OPTIONS --universe-polymorphism #-}
module Categories.Yoneda where

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.Presheaves

Embed : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Presheaves C)
Embed C = record
  { F₀ = λ x → Hom[ C ][-, x ]
  ; F₁ = λ f → record 
    { η = λ X → record 
      { _⟨$⟩_ = λ g → f ∘ g
      ; cong = λ x → ∘-resp-≡ʳ x
      }
    ; commute = commute′ f
    }
  ; identity = λ x≡y → trans identityˡ x≡y
  ; homomorphism = λ x≡y → trans (∘-resp-≡ʳ x≡y) assoc
  ; F-resp-≡ = λ f≡g h≡i → ∘-resp-≡ f≡g h≡i
  }
  where
  open Category C
  open Equiv

  .commute′ : {A B X Y : Obj} (f : A ⇒ B) (g : Y ⇒ X) {x y : X ⇒ A} → x ≡ y → f ∘ id ∘ x ∘ g ≡ id ∘ (f ∘ y) ∘ g
  commute′ f g {x} {y} x≡y = 
    begin
      f ∘ id ∘ x ∘ g
    ↑⟨ assoc ⟩
      (f ∘ id) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ˡ id-comm ⟩
      (id ∘ f) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y) ⟩
      (id ∘ f) ∘ y ∘ g
    ≈⟨ assoc ⟩
      id ∘ f ∘ y ∘ g
    ↑⟨ ∘-resp-≡ʳ assoc ⟩
      id ∘ (f ∘ y) ∘ g
    ∎
    where open HomReasoning
