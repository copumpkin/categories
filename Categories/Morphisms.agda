{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Morphisms {o a} (C : Category o a) where

open import Level
open import Relation.Binary using (IsEquivalence; Setoid)

open import Categories.Support.PropositionalEquality

open Category C

Mono : ∀ {A B} → (f : A ⇒ B) → Set _
Mono {A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂

Epi : ∀ {B A} → (f : A ⇒ B) → Set _
Epi {B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≡ g₂ ∘ f → g₁ ≡ g₂

record Iso {A B} (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊔ a) where
  field
    .isoˡ : g ∘ f ≡ id
    .isoʳ : f ∘ g ≡ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ a) where
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

≅-setoid : Setoid o (o ⊔ a)
≅-setoid = record
  { Carrier = Obj
  ; _≈_ = _≅_
  ; isEquivalence = ≅-is-equivalence
  }

-- equality of isos induced from arrow equality
-- could just use a pair, but this way is probably clearer

record _≡ⁱ_ {A B : Obj} (i j : A ≅ B) : Set (o ⊔ a) where
  open _≅_
  field
    f-≡ : f i ≡ f j
    g-≡ : g i ≡ g j

{-
≡ⁱ-setoid : ∀ {A B} → Setoid (o ⊔ a) (o ⊔ a)
≡ⁱ-setoid {A} {B} = record
  { Carrier = A ≅ B; _≈_ = _≡ⁱ_; isEquivalence = ≡ⁱ-is-equivalence }
-}

-- groupoid with only isos
Coreᵉ : EasyCategory o (o ⊔ a) (o ⊔ a)
Coreᵉ = record
  { Obj = Obj
  ; _⇒_ = _≅_
  ; _≡_ = _≡ⁱ_
  ; id = idⁱ
  ; _∘_ = _ⓘ_
  ; assoc = λ {A B C D f g h} → record { f-≡ = assoc; g-≡ = sym assoc }
  ; identityˡ = λ {A B f} → record { f-≡ = identityˡ; g-≡ = identityʳ }
  ; identityʳ = λ {A B f} → record { f-≡ = identityʳ; g-≡ = identityˡ }
  ; promote = promote
  ; REFL = record { f-≡ = ≣-refl ; g-≡ = ≣-refl }
  }
  where
  open Equiv
  open _≡ⁱ_
  open EasyLaws _≅_ _ⓘ_ idⁱ _≡ⁱ_

  mkiso : ∀ {A B} x u .(z : Iso x u) → A ≅ B
  mkiso = λ x u .z → record { f = x ; g = u ; iso = z }

  promote : Promote
  promote f g f≡g = ≣-cong₂₊ mkiso (_≅_.iso f) (f-≡ f≡g) (g-≡ f≡g)

.≡ⁱ-is-equivalence : ∀ {A B} → IsEquivalence (_≡ⁱ_ {A} {B})
≡ⁱ-is-equivalence = EasyCategory.equiv Coreᵉ

Core = EASY Coreᵉ

-- heterogeneous equality of isos
open Heterogeneous Core public using () renaming (_∼_ to _∼ⁱ_; ≡⇒∼ to ≡⇒∼ⁱ; ∼⇒≡ to ∼⇒≡ⁱ; refl to ∼ⁱ-refl; sym to ∼ⁱ-sym; trans to ~ⁱ-trans; ∘-resp-∼ to ∘-resp-∼ⁱ; ∘-resp-∼ˡ to ∘-resp-∼ⁱˡ; ∘-resp-∼ʳ to ∘-resp-∼ⁱʳ; domain-≣ to domain-≣ⁱ; codomain-≣ to codomain-≣ⁱ)

private
  f-∼′ : ∀ {A B} {i : A ≅ B} {A′ B′} {j : A′ ≅ B′} (eq : i ∼ⁱ j) → Heterogeneous._∼_ C (_≅_.f i) (_≅_.f j)
  f-∼′ (≡⇒∼ⁱ eq) = ≡⇒∼ (≣-cong _≅_.f eq)
    where
    open Heterogeneous C
    open _≡ⁱ_

  g-∼′ : ∀ {A B} {i : A ≅ B} {A′ B′} {j : A′ ≅ B′} (eq : i ∼ⁱ j) → Heterogeneous._∼_ C (_≅_.g i) (_≅_.g j)
  g-∼′ (≡⇒∼ⁱ eq) = ≡⇒∼ (≣-cong _≅_.g eq)
    where
    open Heterogeneous C
    open _≡ⁱ_

-- fake record
module _∼ⁱ_ {A B} {i : A ≅ B} {A′ B′} {j : A′ ≅ B′} (eq : i ∼ⁱ j) where
  open _≅_
  open Heterogeneous C

  f-∼ : f i ∼ f j
  f-∼ = f-∼′ eq

  g-∼ : g i ∼ g j
  g-∼ = g-∼′ eq


heqⁱ : ∀ {A B} (i : A ≅ B) {A′ B′} (j : A′ ≅ B′) → let open _≅_ in let open Heterogeneous C in f i ∼ f j → g i ∼ g j → i ∼ⁱ j
heqⁱ i j (Heterogeneous.≡⇒∼ eq-f) (Heterogeneous.≡⇒∼ eq-g)
  = ≡⇒∼ⁱ {f = i} {g = j} (EasyCategory.promote Coreᵉ i j record { f-≡ = eq-f; g-≡ = eq-g })
