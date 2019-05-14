{-# OPTIONS --universe-polymorphism --irrelevant-projections #-}
open import Categories.Category

module Categories.Morphisms {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary using (IsEquivalence; Setoid)

open Category C

Mono : ∀ {A B} → (f : A ⇒ B) → Set _
Mono {A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂

Epi : ∀ {B A} → (f : A ⇒ B) → Set _
Epi {B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≡ g₂ ∘ f → g₁ ≡ g₂

record Iso {A B} (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    .isoˡ : g ∘ f ≡ id
    .isoʳ : f ∘ g ≡ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    f : A ⇒ B
    g : B ⇒ A
    .iso : Iso f g
  .isoˡ : _
  isoˡ = Iso.isoˡ iso
  .isoʳ : _
  isoʳ = Iso.isoʳ iso

infix 4 _ⓘ_
_ⓘ_ : ∀ {X Y Z} → Y ≅ Z → X ≅ Y → X ≅ Z
G ⓘ F = record
  { f = G.f ∘ F.f
  ; g = F.g ∘ G.g
  ; iso = record
    { isoˡ =
      begin
        (F.g ∘ G.g) ∘ (G.f ∘ F.f)
      ↓⟨ assoc ⟩
        F.g ∘ (G.g ∘ (G.f ∘ F.f))
      ↑⟨ refl ⟩∘⟨ assoc ⟩
        F.g ∘ (G.g ∘ G.f) ∘ F.f
      ↓⟨ refl ⟩∘⟨ G.isoˡ ⟩∘⟨ refl ⟩
        F.g ∘ (id ∘ F.f)
      ↓⟨ refl ⟩∘⟨ identityˡ ⟩
        F.g ∘ F.f
      ↓⟨ F.isoˡ ⟩
        id
      ∎
    ; isoʳ =
      begin
        (G.f ∘ F.f) ∘ (F.g ∘ G.g)
      ↓⟨ assoc ⟩
        G.f ∘ (F.f ∘ (F.g ∘ G.g))
      ↑⟨ refl ⟩∘⟨ assoc ⟩
        G.f ∘ (F.f ∘ F.g) ∘ G.g
      ↓⟨ refl ⟩∘⟨ F.isoʳ ⟩∘⟨ refl ⟩
        G.f ∘ (id ∘ G.g)
      ↓⟨ refl ⟩∘⟨ identityˡ ⟩
        G.f ∘ G.g
      ↓⟨ G.isoʳ ⟩
        id
      ∎
    }
  }
  where
  module F = _≅_ F
  module G = _≅_ G
  open Iso
  open Equiv
  open HomReasoning

idⁱ : ∀ {A} → A ≅ A
idⁱ {A} = record
  { f = id
  ; g = id
  ; iso = record
    { isoˡ = identityˡ
    ; isoʳ = identityˡ
    }
  }

reverseⁱ : ∀ {A B} → A ≅ B → B ≅ A
reverseⁱ A≅B = record
  { f = A≅B.g
  ; g = A≅B.f
  ; iso = record
    { isoˡ = A≅B.isoʳ
    ; isoʳ = A≅B.isoˡ
    }
  }
  where
  module A≅B = _≅_ A≅B

≅-is-equivalence : IsEquivalence _≅_
≅-is-equivalence = record
  { refl = idⁱ
  ; sym = reverseⁱ
  ; trans = λ x y → y ⓘ x
  }

≅-setoid : Setoid o (o ⊔ ℓ ⊔ e)
≅-setoid = record
  { Carrier = Obj
  ; _≈_ = _≅_
  ; isEquivalence = ≅-is-equivalence
  }

-- equality of isos induced from arrow equality
-- could just use a pair, but this way is probably clearer

record _≡ⁱ_ {A B : Obj} (i j : A ≅ B) : Set (o ⊔ ℓ ⊔ e) where
  open _≅_
  field
    f-≡ : f i ≡ f j
    g-≡ : g i ≡ g j

.≡ⁱ-is-equivalence : ∀ {A B} → IsEquivalence (_≡ⁱ_ {A} {B})
≡ⁱ-is-equivalence = record
  { refl = record { f-≡ = refl; g-≡ = refl }
  ; sym = λ x → record { f-≡ = sym (f-≡ x); g-≡ = sym (g-≡ x) }
  ; trans = λ x y → record { f-≡ = trans (f-≡ x) (f-≡ y); g-≡ = trans (g-≡ x) (g-≡ y) }
  }
  where
  open Equiv
  open _≡ⁱ_

{-
≡ⁱ-setoid : ∀ {A B} → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
≡ⁱ-setoid {A} {B} = record
  { Carrier = A ≅ B; _≈_ = _≡ⁱ_; isEquivalence = ≡ⁱ-is-equivalence }
-}

-- groupoid with only isos
Isos : Category o (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Isos = record
  { Obj = Obj
  ; _⇒_ = _≅_
  ; _≡_ = _≡ⁱ_
  ; id = idⁱ
  ; _∘_ = _ⓘ_
  ; assoc = λ {A B C D f g h} → record { f-≡ = assoc; g-≡ = sym assoc }
  ; identityˡ = λ {A B f} → record { f-≡ = identityˡ; g-≡ = identityʳ }
  ; identityʳ = λ {A B f} → record { f-≡ = identityʳ; g-≡ = identityˡ }
  ; equiv = ≡ⁱ-is-equivalence
  ; ∘-resp-≡ = λ {A B C f h g i} f≡ⁱh g≡ⁱi → record
    { f-≡ = ∘-resp-≡ (f-≡ f≡ⁱh) (f-≡ g≡ⁱi)
    ; g-≡ = ∘-resp-≡ (g-≡ g≡ⁱi) (g-≡ f≡ⁱh)
    }
  }
  where
  open Equiv
  open _≡ⁱ_

-- heterogeneous equality of isos
open Heterogeneous Isos public using () renaming (_∼_ to _∼ⁱ_; ≡⇒∼ to ≡⇒∼ⁱ; ∼⇒≡ to ∼⇒≡ⁱ; refl to ∼ⁱ-refl; sym to ∼ⁱ-sym; trans to ~ⁱ-trans; ∘-resp-∼ to ∘-resp-∼ⁱ; ∘-resp-∼ˡ to ∘-resp-∼ⁱˡ; ∘-resp-∼ʳ to ∘-resp-∼ⁱʳ; domain-≣ to domain-≣ⁱ; codomain-≣ to codomain-≣ⁱ)

private
  f-∼′ : ∀ {A B} {i : A ≅ B} {A′ B′} {j : A′ ≅ B′} (eq : i ∼ⁱ j) → Heterogeneous._∼_ C (_≅_.f i) (_≅_.f j)
  f-∼′ (≡⇒∼ⁱ eq) = ≡⇒∼ (f-≡ eq)
    where
    open Heterogeneous C
    open _≡ⁱ_

  g-∼′ : ∀ {A B} {i : A ≅ B} {A′ B′} {j : A′ ≅ B′} (eq : i ∼ⁱ j) → Heterogeneous._∼_ C (_≅_.g i) (_≅_.g j)
  g-∼′ (≡⇒∼ⁱ eq) = ≡⇒∼ (g-≡ eq)
    where
    open Heterogeneous C
    open _≡ⁱ_

heqⁱ : ∀ {A B} (i : A ≅ B) {A′ B′} (j : A′ ≅ B′) → let open _≅_ in let open Heterogeneous C in f i ∼ f j → g i ∼ g j → i ∼ⁱ j
heqⁱ i j (Heterogeneous.≡⇒∼ eq-f) (Heterogeneous.≡⇒∼ eq-g)
  = ≡⇒∼ⁱ {f = i} {g = j} (record { f-≡ = eq-f; g-≡ = eq-g })
