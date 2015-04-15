{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.BinaryProducts {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level

import Categories.Object.Product as Product
import Categories.Object.Product.Morphisms as ProductMorphisms

open import Categories.Morphisms C

open Product C
open ProductMorphisms C

record BinaryProducts : Set (o ⊔ ℓ ⊔ e) where

  infixr 2 _×_
  infix 10 _⁂_

  field
    product : ∀ {A B} → Product A B

  _×_ : Obj → Obj → Obj
  A × B = Product.A×B (product {A} {B})

  ×-comm : ∀ {A B} → _≅_ (A × B) (B × A)
  ×-comm = Commutative product product

  ×-assoc : ∀ {X Y Z} → _≅_ (X × (Y × Z)) ((X × Y) × Z)
  ×-assoc = Associative product product product product

  -- Convenience!
  π₁ : {A B : Obj} → ((A × B) ⇒ A)
  π₁ = Product.π₁ product

  π₂ : {A B : Obj} → ((A × B) ⇒ B)
  π₂ = Product.π₂ product

  ⟨_,_⟩ : ∀ {A B Q} → (Q ⇒ A) → (Q ⇒ B) → (Q ⇒ (A × B))
  ⟨_,_⟩ = Product.⟨_,_⟩ product

  .commute₁ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
  commute₁ = Product.commute₁ product

  .commute₂ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
  commute₂ = Product.commute₂ product

  .universal : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ (A × B)}
               → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i
  universal = Product.universal product

  assocˡ : ∀ {A B C} → (((A × B) × C) ⇒ (A × (B × C)))
  assocˡ = _≅_.g ×-assoc

  assocʳ : ∀ {A B C} → ((A × (B × C)) ⇒ ((A × B) × C))
  assocʳ = _≅_.f ×-assoc

  .assocʳ∘assocˡ : ∀ {A B C} → assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≡ id
  assocʳ∘assocˡ = Iso.isoʳ (_≅_.iso ×-assoc)
  
  .assocˡ∘assocʳ : ∀ {A B C} → assocˡ {A}{B}{C} ∘ assocʳ {A}{B}{C} ≡ id
  assocˡ∘assocʳ = Iso.isoˡ (_≅_.iso ×-assoc)
  
  .g-η : ∀ {A B C} {f : C ⇒ (A × B)} → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f
  g-η = Product.g-η product

  .η : ∀ {A B} → ⟨ π₁ , π₂ ⟩ ≡ id {A × B}
  η = Product.η product

  .⟨⟩-cong₂ : ∀ {A B C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ = Product.⟨⟩-cong₂ product
  
  .⟨⟩-congˡ : ∀ {A B C} → {f f′ : C ⇒ A} {g : C ⇒ B} → f ≡ f′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g ⟩
  ⟨⟩-congˡ pf = ⟨⟩-cong₂ pf refl
  
  .⟨⟩-congʳ : ∀ {A B C} → {f : C ⇒ A} {g g′ : C ⇒ B} → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f , g′ ⟩
  ⟨⟩-congʳ pf = ⟨⟩-cong₂ refl pf
  
  _⁂_ : ∀ {A B C D} → (A ⇒ B) → (C ⇒ D) → ((A × C) ⇒ (B × D))
  f ⁂ g = [ product ⇒ product ] f ⁂ g
  
  swap : ∀ {A B} → ((A × B) ⇒ (B × A))
  swap = ⟨ π₂ , π₁ ⟩
  
  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  first : ∀ {A B C} → (A ⇒ B) → ((A × C) ⇒ (B × C))
  first f = f ⁂ id

  second : ∀ {A C D} → (C ⇒ D) → ((A × C) ⇒ (A × D))
  second g = id ⁂ g

  -- Just to make this more obvious
  .π₁∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → π₁ ∘ (f ⁂ g) ≡ f ∘ π₁
  π₁∘⁂ {f = f} {g} = commute₁

  .π₂∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → π₂ ∘ (f ⁂ g) ≡ g ∘ π₂
  π₂∘⁂ {f = f} {g} = commute₂

  .⁂-cong₂ : ∀ {A B C D}{f g : A ⇒ B}{h i : C ⇒ D}
    → f ≡ g → h ≡ i → f ⁂ h ≡ g ⁂ i
  ⁂-cong₂ = [ product ⇒ product ]⁂-cong₂

  .⁂∘⟨⟩ : ∀ {A B C D E} → {f : B ⇒ C} {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ⁂∘⟨⟩ = [ product ⇒ product ]⁂∘⟨⟩

  .first∘⟨⟩ : ∀ {A B C D} → {f : B ⇒ C} {f′ : A ⇒ B} {g′ : A ⇒ D} → first f ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ = [ product ⇒ product ]first∘⟨⟩

  .second∘⟨⟩ : ∀ {A B D E} → {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → second g ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ = [ product ⇒ product ]second∘⟨⟩

  .⁂∘⁂ : ∀ {A B C D E F} → {f : B ⇒ C} → {f′ : A ⇒ B} {g : E ⇒ F} {g′ : D ⇒ E} → (f ⁂ g) ∘ (f′ ⁂ g′) ≡ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂∘⁂ = [ product ⇒ product ⇒ product ]⁂∘⁂
  
  .⟨⟩∘ : ∀ {A B C D} {f : A ⇒ B} {g : A ⇒ C} {q : D ⇒ A} → ⟨ f , g ⟩ ∘ q ≡ ⟨ f ∘ q , g ∘ q ⟩
  ⟨⟩∘ = sym (universal (trans (sym assoc) (∘-resp-≡ˡ commute₁)) (trans (sym assoc) (∘-resp-≡ˡ commute₂)))
  
  .first∘first : ∀ {A B C D}{f : B ⇒ C} {g : A ⇒ B}
    → first f ∘ first g ≡ first {C = D} (f ∘ g)
  first∘first = [ product ⇒ product ⇒ product ]first∘first
  
  .second∘second : ∀ {A B C D}{f : B ⇒ C} {g : A ⇒ B}
    → second f ∘ second g ≡ second {A = D} (f ∘ g)
  second∘second = [ product ⇒ product ⇒ product ]second∘second
    
  .first↔second : ∀ {A B C D}{f : A ⇒ B}{g : C ⇒ D}
    → first f ∘ second g ≡ second g ∘ first f
  first↔second = [ product ⇒ product , product ⇒ product ]first↔second
  
  .swap∘⟨⟩ : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C}
    → swap ∘ ⟨ f , g ⟩ ≡ ⟨ g , f ⟩
  swap∘⟨⟩ {A}{B}{C}{f}{g} =
    begin
      ⟨ π₂ , π₁ ⟩ ∘ ⟨ f , g ⟩
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ π₂ ∘ ⟨ f , g ⟩ , π₁ ∘ ⟨ f , g ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ commute₂ commute₁ ⟩
      ⟨ g , f ⟩
    ∎ where open HomReasoning

  .swap∘⁂ : ∀ {A B C D} {f : A ⇒ B} {g : C ⇒ D}
    → swap ∘ (f ⁂ g) ≡ (g ⁂ f) ∘ swap
  swap∘⁂ {f = f}{g} =
    begin
      swap ∘ (f ⁂ g)
    ↓⟨ swap∘⟨⟩ ⟩
      ⟨ g ∘ π₂ , f ∘ π₁ ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      (g ⁂ f) ∘ swap
    ∎ where open HomReasoning
  
  .swap∘swap : ∀ {A B} → (swap {A}{B}) ∘ (swap {B}{A}) ≡ id
  swap∘swap = trans swap∘⟨⟩ η
  
  .assocʳ∘⟨⟩ : ∀ {A B C D} {f : A ⇒ B} {g : A ⇒ C} {h : A ⇒ D}
    → assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≡ ⟨ ⟨ f , g ⟩ , h ⟩
  assocʳ∘⟨⟩ {f = f}{g}{h} =
    begin
      assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ 
      , (π₂ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩ 
      ⟩
    ↓⟨ ⟨⟩-cong₂ ⟨⟩∘ assoc ⟩
      ⟨ ⟨ π₁        ∘ ⟨ f , ⟨ g , h ⟩ ⟩ 
        , (π₁ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩ 
        ⟩
      , π₂ ∘ π₂ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ 
      ⟩
    ↓⟨ ⟨⟩-cong₂ (⟨⟩-cong₂ commute₁ assoc ) (∘-resp-≡ʳ commute₂) ⟩
      ⟨ ⟨ f , π₁ ∘ π₂ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ⟩
      , π₂ ∘ ⟨ g , h ⟩ 
      ⟩
    ↓⟨ ⟨⟩-cong₂ (⟨⟩-congʳ (∘-resp-≡ʳ commute₂)) commute₂ ⟩
      ⟨ ⟨ f , π₁ ∘ ⟨ g , h ⟩ ⟩ , h ⟩
    ↓⟨ ⟨⟩-congˡ (⟨⟩-congʳ commute₁) ⟩
      ⟨ ⟨ f , g ⟩ , h ⟩
    ∎ where open HomReasoning
  
  .assocˡ∘⟨⟩ : ∀ {A B C D} {f : A ⇒ B} {g : A ⇒ C} {h : A ⇒ D}
    → assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩ ≡ ⟨ f , ⟨ g , h ⟩ ⟩
  assocˡ∘⟨⟩ {f = f}{g}{h} =
    begin
      assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩
    ↑⟨ refl ⟩∘⟨ assocʳ∘⟨⟩ ⟩
      assocˡ ∘ assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ↑⟨ assoc ⟩
      (assocˡ ∘ assocʳ) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ↓⟨ assocˡ∘assocʳ ⟩∘⟨ refl ⟩
      id ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ↓⟨ identityˡ ⟩
      ⟨ f , ⟨ g , h ⟩ ⟩
    ∎ where open HomReasoning
  
  .assocʳ∘⁂ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂} {f : A₁ ⇒ A₂} {g : B₁ ⇒ B₂} {h : C₁ ⇒ C₂}
    → assocʳ ∘ (f ⁂ (g ⁂ h)) ≡ ((f ⁂ g) ⁂ h) ∘ assocʳ
  assocʳ∘⁂ {f = f}{g}{h} = 
    begin
      assocʳ ∘ (f ⁂ (g ⁂ h))
    ↓⟨ refl ⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ (g ∘ π₁) ∘ π₂ , (h ∘ π₂) ∘ π₂ ⟩ ⟩
    ↓⟨ assocʳ∘⟨⟩ ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , (h ∘ π₂) ∘ π₂ ⟩
    ↓⟨ ⟨⟩-cong₂ (⟨⟩-congʳ assoc) assoc ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ↑⟨ ⟨⟩-congˡ ⁂∘⟨⟩ ⟩
      ⟨ (f ⁂ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      ((f ⁂ g) ⁂ h) ∘ assocʳ
    ∎ where open HomReasoning
  
  .assocˡ∘⁂ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂} {f : A₁ ⇒ A₂} {g : B₁ ⇒ B₂} {h : C₁ ⇒ C₂}
    → assocˡ ∘ ((f ⁂ g) ⁂ h) ≡ (f ⁂ (g ⁂ h)) ∘ assocˡ
  assocˡ∘⁂ {f = f}{g}{h} = 
    begin
      assocˡ ∘ ((f ⁂ g) ⁂ h)
    ↓⟨ refl ⟩∘⟨ ⟨⟩-congˡ ⟨⟩∘ ⟩
      assocˡ ∘ ⟨ ⟨ (f ∘ π₁) ∘ π₁ , (g ∘ π₂) ∘ π₁ ⟩ , h ∘ π₂ ⟩
    ↓⟨ assocˡ∘⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (g ∘ π₂) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ assoc (⟨⟩-congˡ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ↑⟨ ⟨⟩-congʳ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ π₁ ∘ π₁ , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      (f ⁂ (g ⁂ h)) ∘ assocˡ
    ∎ where open HomReasoning
