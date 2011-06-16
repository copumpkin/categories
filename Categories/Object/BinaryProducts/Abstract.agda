{-# OPTIONS --universe-polymorphism #-}
module Categories.Object.BinaryProducts.Abstract where

open import Categories.Support.PropositionalEquality
open import Categories.Category
open import Categories.Object.BinaryProducts
open import Categories.Morphisms

module AbstractBinaryProducts {o ℓ e} (C : Category o ℓ e) (BP : BinaryProducts C) where
  private module P = BinaryProducts C BP
  open P public using (_×_; π₁; π₂)
  private open Category C
  private import Categories.Object.Product as Product

  mutual
    first : ∀ {A B C} → (A ⇒ B) → ((A × C) ⇒ (B × C))
    first f = f ⁂ id

    second : ∀ {A C D} → (C ⇒ D) → ((A × C) ⇒ (A × D))
    second g = id ⁂ g

    abstract
      infix 10 _⁂_

      _⁂_ : ∀ {A B C D} → (A ⇒ B) → (C ⇒ D) → ((A × C) ⇒ (B × D))
      _⁂_ = P._⁂_

      ⟨_,_⟩ : ∀ {A B Q} → (Q ⇒ A) → (Q ⇒ B) → (Q ⇒ (A × B))
      ⟨_,_⟩ = P.⟨_,_⟩

      ⁂-convert : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → f ⁂ g ≣ ⟨ f ∘ π₁ , g ∘ π₂ ⟩
      ⁂-convert f g = ≣-refl

      assocˡ : ∀ {A B C} → (((A × B) × C) ⇒ (A × (B × C)))
      assocˡ = P.assocˡ

      assocˡ-convert : ∀ {A B C} → assocˡ {A} {B} {C} ≣ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      assocˡ-convert = ≣-refl

      assocʳ : ∀ {A B C} → ((A × (B × C)) ⇒ ((A × B) × C))
      assocʳ = P.assocʳ

      assocʳ-convert : ∀ {A B C} → assocʳ {A} {B} {C} ≣ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      assocʳ-convert = ≣-refl

      .assoc-iso : ∀ {A B C′} → Iso C (assocʳ {A} {B} {C′}) assocˡ
      assoc-iso = _≅_.iso C P.×-assoc

      .⁂∘⁂ : ∀ {A B C D E F} → {f : B ⇒ C} → {f′ : A ⇒ B} {g : E ⇒ F} {g′ : D ⇒ E} → (f ⁂ g) ∘ (f′ ⁂ g′) ≡ (f ∘ f′) ⁂ (g ∘ g′)
      ⁂∘⁂ = P.⁂∘⁂

      .⁂∘⟨⟩ : ∀ {A B C D E} → {f : B ⇒ C} {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g ∘ g′ ⟩
      ⁂∘⟨⟩ = P.⁂∘⟨⟩

      .π₁∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → π₁ ∘ (f ⁂ g) ≡ f ∘ π₁
      π₁∘⁂ = P.π₁∘⁂

      .π₂∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → π₂ ∘ (f ⁂ g) ≡ g ∘ π₂
      π₂∘⁂ = P.π₂∘⁂

      .⟨⟩-cong₂ : ∀ {A B C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
      ⟨⟩-cong₂ = P.⟨⟩-cong₂

      .⟨⟩∘ : ∀ {A B C D} {f : A ⇒ B} {g : A ⇒ C} {q : D ⇒ A} → ⟨ f , g ⟩ ∘ q ≡ ⟨ f ∘ q , g ∘ q ⟩
      ⟨⟩∘ = P.⟨⟩∘

      .first∘⟨⟩ : ∀ {A B C D} → {f : B ⇒ C} {f′ : A ⇒ B} {g′ : A ⇒ D} → first f ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g′ ⟩
      first∘⟨⟩ = P.first∘⟨⟩

      .second∘⟨⟩ : ∀ {A B D E} → {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → second g ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f′ , g ∘ g′ ⟩
      second∘⟨⟩ = P.second∘⟨⟩

      .η : ∀ {A B} → ⟨ π₁ , π₂ ⟩ ≡ id {A × B}
      η = P.η

      .commute₁ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
      commute₁ = P.commute₁

      .commute₂ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
      commute₂ = P.commute₂

      .universal : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ (A × B)}
                   → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i
      universal = P.universal

  module HomReasoningP {A B : Obj} where
    open HomReasoning {A} {B} public

    -- sort of a hack, if you specify the codomain for your top-level
    --   reasoning you will NOT get what you want from the below
    infix 3 ⟨_⟩,⟨_⟩
    .⟨_⟩,⟨_⟩ : ∀ {C} → {f f′ : A ⇒ B} {g g′ : A ⇒ C} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
    ⟨_⟩,⟨_⟩ x y = ⟨⟩-cong₂ x y