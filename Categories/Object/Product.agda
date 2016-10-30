{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Product {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Function using (flip)
open import Level
open import Function using (flip)
open import Categories.Support.PropositionalEquality

open import Categories.Square
open GlueSquares C

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where

  infix 10 ⟨_,_⟩

  field
    A×B : Obj
    π₁ : A×B ⇒ A
    π₂ : A×B ⇒ B
    ⟨_,_⟩ : ∀ {C} → (C ⇒ A) → (C ⇒ B) → (C ⇒ A×B)

    .commute₁ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
    .commute₂ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
    .universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ A×B}
               → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i

  .g-η : ∀ {C} {f : C ⇒ A×B} → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f
  g-η = universal refl refl

  .η : ⟨ π₁ , π₂ ⟩ ≡ id
  η = universal identityʳ identityʳ

  .⟨⟩-cong₂ : ∀ {C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≡f′ g≡g′ = 
    universal (trans commute₁ (sym f≡f′)) (trans commute₂ (sym g≡g′))

  .⟨⟩∘ : ∀ {C D} {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} → ⟨ f , g ⟩ ∘ q ≡ ⟨ f ∘ q , g ∘ q ⟩
  ⟨⟩∘ = sym (universal (pullˡ commute₁) (pullˡ commute₂))


import Categories.Morphisms
open Categories.Morphisms C

private 
  module Lemmas {A B : Obj} where
    open Product {A} {B} renaming (⟨_,_⟩ to _⟨_,_⟩)

    repack : (p₁ p₂ : Product A B) → A×B p₁ ⇒ A×B p₂
    repack p₁ p₂ = p₂ ⟨ π₁ p₁ , π₂ p₁ ⟩

    .repack∘ : (p₁ p₂ p₃ : Product A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≡ repack p₁ p₃
    repack∘ p₁ p₂ p₃ = sym (universal p₃ 
      (glueTrianglesʳ (commute₁ p₃) (commute₁ p₂))
      (glueTrianglesʳ (commute₂ p₃) (commute₂ p₂)))

    .repack≡id : (p : Product A B) → repack p p ≡ id
    repack≡id p = η p

    .repack-cancel : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≡ id
    repack-cancel p₁ p₂ = trans (repack∘ p₂ p₁ p₂) (repack≡id p₂)

up-to-iso : ∀ {A B} → (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
up-to-iso p₁ p₂ = record
  { f = repack p₁ p₂
  ; g = repack p₂ p₁
  ; iso = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }
  where
  open Lemmas

transport-by-iso : ∀ {A B} → (p : Product A B) → ∀ {X} → Product.A×B p ≅ X → Product A B
transport-by-iso p {X} p≅X = record
  { A×B = X
  ; π₁ = p.π₁ ∘ g
  ; π₂ = p.π₂ ∘ g
  ; ⟨_,_⟩ = λ h₁ h₂ → f ∘ p ⟨ h₁ , h₂ ⟩
  ; commute₁ = trans (cancelInner isoˡ) p.commute₁
  ; commute₂ = trans (cancelInner isoˡ) p.commute₂
  ; universal = λ {_ l r i} pfˡ pfʳ → let open HomReasoning in
      begin
        f ∘ p ⟨ l , r ⟩
      ↑⟨ ∘-resp-≡ʳ (p.⟨⟩-cong₂ pfˡ pfʳ) ⟩
        f ∘ p ⟨ (p.π₁ ∘ g) ∘ i , (p.π₂ ∘ g) ∘ i ⟩
      ↓⟨ ∘-resp-≡ʳ (p.universal (sym assoc) (sym assoc)) ⟩
        f ∘ (g ∘ i)
      ↓⟨ cancelLeft isoʳ ⟩
        i
      ∎
  }
  where
  module p = Product p
  open Product using () renaming (⟨_,_⟩ to _⟨_,_⟩) 
  open _≅_ p≅X

Reversible : ∀ {A B} → (p : Product A B) → Product B A
Reversible p = record
  { A×B = p.A×B
  ; π₁ = p.π₂
  ; π₂ = p.π₁
  ; ⟨_,_⟩ = flip p.⟨_,_⟩
  ; commute₁ = p.commute₂
  ; commute₂ = p.commute₁
  ; universal = flip p.universal
  }
  where module p = Product p

Commutative : ∀ {A B} (p₁ : Product A B) (p₂ : Product B A) → Product.A×B p₁ ≅ Product.A×B p₂
Commutative p₁ p₂ = up-to-iso p₁ (Reversible p₂)

Associable : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) → Product (Product.A×B p₁) Z
Associable p₁ p₂ p₃ = record
  { A×B = A×B p₃
  ; π₁ = p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩
  ; π₂ = π₂ p₂ ∘ π₂ p₃
  ; ⟨_,_⟩ = λ f g → p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
  ; commute₁ = λ {_ f g} → let open HomReasoning in begin
      p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
    ↓⟨ ⟨⟩∘ p₁ ⟩
      p₁ ⟨ π₁ p₃ ∘ p₃ ⟨ π₁ p₁ ∘ f , _ ⟩ , (π₁ p₂ ∘ π₂ p₃) ∘ p₃ ⟨ _ , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₁ (commute₁ p₃) (glueTrianglesˡ (commute₁ p₂) (commute₂ p₃)) ⟩
      p₁ ⟨ π₁ p₁ ∘ f , π₂ p₁ ∘ f ⟩
    ↓⟨ g-η p₁ ⟩
      f
    ∎
  ; commute₂ = λ {_ f g} → glueTrianglesˡ (commute₂ p₂) (commute₂ p₃)
  ; universal = λ {D l r i} pfˡ pfʳ → let open HomReasoning in begin
      p₃ ⟨ π₁ p₁ ∘ l , p₂ ⟨ π₂ p₁ ∘ l , r ⟩ ⟩
    ↑⟨ ⟨⟩-cong₂ p₃ (∘-resp-≡ʳ pfˡ) (⟨⟩-cong₂ p₂ (∘-resp-≡ʳ pfˡ) pfʳ) ⟩
      p₃ ⟨ π₁ p₁ ∘ (p₁ ⟨ π₁ p₃ , _ ⟩ ∘ i) , p₂ ⟨ π₂ p₁ ∘ (p₁ ⟨ _ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i) , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₃ (pullˡ (commute₁ p₁)) (⟨⟩-cong₂ p₂ (pullˡ (commute₂ p₁)) refl) ⟩
      p₃ ⟨ π₁ p₃ ∘ i , p₂ ⟨ (π₁ p₂ ∘ π₂ p₃) ∘ i , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₃ refl (universal p₂ (sym assoc) (sym assoc)) ⟩
      p₃ ⟨ π₁ p₃ ∘ i , π₂ p₃ ∘ i ⟩
    ↓⟨ g-η p₃ ⟩
      i
    ∎
  }
  where
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)

Associative : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) → (Product.A×B p₃) ≅ (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = up-to-iso (Associable p₁ p₂ p₃) p₄

open Lemmas public

Mobile : ∀ {A₁ B₁ A₂ B₂} (p : Product A₁ B₁) → A₁ ≅ A₂ → B₁ ≅ B₂ → Product A₂ B₂
Mobile p A₁≅A₂ B₁≅B₂ = record
  { A×B = p.A×B
  ; π₁ = f A₁≅A₂ ∘ p.π₁
  ; π₂ = f B₁≅B₂ ∘ p.π₂
  ; ⟨_,_⟩ = λ h k → p ⟨ g A₁≅A₂ ∘ h , g B₁≅B₂ ∘ k ⟩
  ; commute₁ = let open HomReasoning in begin
      (f A₁≅A₂ ∘ p.π₁) ∘ p ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩
    ↓⟨ pullʳ p.commute₁ ⟩
      f A₁≅A₂ ∘ (g A₁≅A₂ ∘ _)
    ↓⟨ cancelLeft (isoʳ A₁≅A₂) ⟩
      _
    ∎
  ; commute₂ = let open HomReasoning in begin
      (f B₁≅B₂ ∘ p.π₂) ∘ p ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩
    ↓⟨ pullʳ p.commute₂ ⟩
      f B₁≅B₂ ∘ (g B₁≅B₂ ∘ _)
    ↓⟨ cancelLeft (isoʳ B₁≅B₂) ⟩
      _
    ∎
  ; universal = λ pfˡ pfʳ → p.universal 
                              (switch-fgˡ A₁≅A₂ (trans (sym assoc) pfˡ))
                              (switch-fgˡ B₁≅B₂ (trans (sym assoc) pfʳ))
  }
  where
  module p = Product p
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)
  open _≅_
