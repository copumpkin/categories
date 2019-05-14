{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Terminal {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary using (IsEquivalence; Setoid)
open import Categories.Support.PropositionalEquality

open Category C

record Terminal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤ : Obj
    ! : ∀ {A} → (A ⇒ ⊤)
    .!-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≡ f

  .!-unique₂ : ∀ {A} → (f g : A ⇒ ⊤) → f ≡ g
  !-unique₂ f g =
    begin
      f
    ↑⟨ !-unique f ⟩
      !
    ↓⟨ !-unique g ⟩
      g
    ∎
    where open HomReasoning

  .⊤-id : (f : ⊤ ⇒ ⊤) → f ≡ id
  ⊤-id f = !-unique₂ f id

  open Heterogeneous C

  !-unique∼ : ∀ {A A′} → (f : A′ ⇒ ⊤) → (A ≣ A′) → ! {A} ∼ f
  !-unique∼ f ≣-refl = Heterogeneous.≡⇒∼ (!-unique f)

import Categories.Morphisms
open Categories.Morphisms C
open Terminal

.from-⊤-is-Mono : ∀ {A : Obj} {t : Terminal} → (f : ⊤ t ⇒ A) → Mono f
from-⊤-is-Mono {_} {t} f = helper
  where
    helper : ∀ {C : Obj} -> (g h : C ⇒ ⊤ t) → f ∘ g ≡ f ∘ h → g ≡ h
    helper g h _ = !-unique₂ t g h

open import Categories.Square
open GlueSquares C
open Heterogeneous C

!-is-propertylike : ∀ t₁ t₂ → ⊤ t₁ ≣ ⊤ t₂ → ∀ {A} → ! t₁ {A} ∼ ! t₂ {A}
!-is-propertylike t₁ t₂ eq = helper t₁ eq (! t₂)
  where
  helper : ∀ t {T} → (⊤ t ≣ T) → ∀ {A} (f : A ⇒ T) → ! t {A} ∼ f
  helper t ≣-refl f = ≡⇒∼ (!-unique t f)

up-to-iso : (t₁ t₂ : Terminal) → ⊤ t₁ ≅ ⊤ t₂
up-to-iso t₁ t₂ = record
  { f = ! t₂
  ; g = ! t₁
  ; iso = record { isoˡ = ⊤-id t₁ _; isoʳ = ⊤-id t₂ _ }
  }

up-to-iso-cong₂ : {t₁ t₁′ t₂ t₂′ : Terminal} → ⊤ t₁ ≣ ⊤ t₁′ → ⊤ t₂ ≣ ⊤ t₂′ → up-to-iso t₁ t₂ ∼ⁱ up-to-iso t₁′ t₂′
up-to-iso-cong₂ {t₁} {t₁′} {t₂} {t₂′} eq₁ eq₂ = heqⁱ (up-to-iso t₁ t₂) (up-to-iso t₁′ t₂′) (helper t₂ t₂′ eq₂ eq₁) (helper t₁ t₁′ eq₁ eq₂)
  where
  helper : ∀ t t′ → (⊤ t ≣ ⊤ t′) → ∀ {A A′} → A ≣ A′ → ! t {A} ∼ ! t′ {A′}
  helper t t′ eq-t ≣-refl = !-is-propertylike t t′ eq-t 

transport-by-iso : (t : Terminal) → ∀ {X} → ⊤ t ≅ X → Terminal
transport-by-iso t {X} t≅X = record
  { ⊤ = X
  ; ! = f ∘ ! t
  ; !-unique = λ h → let open HomReasoning in 
      begin
        f ∘ ! t
      ↓⟨ ∘-resp-≡ʳ (!-unique t (g ∘ h)) ⟩
        f ∘ (g ∘ h)
      ↓⟨ cancelLeft isoʳ ⟩
        h
      ∎
  }
  where open _≅_ t≅X

transport-by-iso-cong₂ : ∀ {t t′} → (⊤ t ≣ ⊤ t′) → ∀ {X} {i : ⊤ t ≅ X} {X′} {i′ : ⊤ t′ ≅ X′} → (i ∼ⁱ i′) → ⊤ (transport-by-iso t i) ≣ ⊤ (transport-by-iso t′ i′)
transport-by-iso-cong₂ eq-t eq-i = codomain-≣ⁱ eq-i

.up-to-iso-unique : ∀ t t′ → (i : ⊤ t ≅ ⊤ t′) → up-to-iso t t′ ≡ⁱ i
up-to-iso-unique t t′ i = record { f-≡ = !-unique t′ _; g-≡ = !-unique t _ }

.up-to-iso-invˡ : ∀ {t X} {i : ⊤ t ≅ X} → up-to-iso t (transport-by-iso t i) ≡ⁱ i
up-to-iso-invˡ {t} {i = i} = up-to-iso-unique t (transport-by-iso t i) i

up-to-iso-invʳ : ∀ {t t′} → ⊤ (transport-by-iso t (up-to-iso t t′)) ≣ ⊤ t′
up-to-iso-invʳ {t} {t′} = ≣-refl
