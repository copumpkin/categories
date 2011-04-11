{-# OPTIONS --universe-polymorphism #-}
open import Category

module Category.Object.BinaryProducts {o ℓ e} (C : Category o ℓ e) where

open import Support hiding (_×_; ⟨_,_⟩)
open Category.Category C
import Category.Object.Product as Product
open import Category.Morphisms

open Product C

record BinaryProducts : Set (o ⊔ ℓ ⊔ e) where
  infix 10 _⁂_

  field
    product : ∀ {A B} → Product A B

  _×_ : Obj → Obj → Obj
  A × B = Product.A×B (product {A} {B})

  ×-comm : ∀ {A B} → _≅_ C (A × B) (B × A)
  ×-comm = Commutative product product

  ×-assoc : ∀ {X Y Z} → _≅_ C (X × (Y × Z)) ((X × Y) × Z)
  ×-assoc = Associative product product product product

  -- Convenience!
  π₁ : {A B : Obj} → Hom (A × B) A
  π₁ = Product.π₁ product

  π₂ : {A B : Obj} → Hom (A × B) B
  π₂ = Product.π₂ product

  ⟨_,_⟩ : ∀ {A B Q} → Hom Q A → Hom Q B → Hom Q (A × B)
  ⟨_,_⟩ = Product.⟨_,_⟩ product

  .commute₁ : ∀ {A B C} {f : Hom C A} {g : Hom C B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
  commute₁ = Product.commute₁ product

  .commute₂ : ∀ {A B C} {f : Hom C A} {g : Hom C B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
  commute₂ = Product.commute₂ product

  .universal : ∀ {A B C} {f : Hom C A} {g : Hom C B} {i : Hom C (A × B)}
               → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i
  universal = Product.universal product

  assocˡ : ∀ {A B C} → Hom ((A × B) × C) (A × (B × C))
  assocˡ = _≅_.g C ×-assoc

  assocʳ : ∀ {A B C} → Hom (A × (B × C)) ((A × B) × C)
  assocʳ = _≅_.f C ×-assoc

  .g-η : ∀ {A B C} {f : Hom C (A × B)} → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f
  g-η = Product.g-η product

  .η : ∀ {A B} → ⟨ π₁ , π₂ ⟩ ≡ id {A × B}
  η = Product.η product

  .⟨⟩-cong₂ : ∀ {A B C} → {f f′ : Hom C A} {g g′ : Hom C B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ = Product.⟨⟩-cong₂ product
  
  -- If I _really_ wanted to, I could do this for a specific pair of products like the rest above, but I'll write that one
  -- when I need it.
  _⁂_ : ∀ {A B C D} → Hom A B → Hom C D → Hom (A × C) (B × D)
  f ⁂ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  first : ∀ {A B C} → Hom A B → Hom (A × C) (B × C)
  first f = f ⁂ id

  second : ∀ {A C D} → Hom C D → Hom (A × C) (A × D)
  second g = id ⁂ g

  -- Just to make this more obvious
  .π₁∘⁂ : ∀ {A B C D} → {f : Hom A B} → {g : Hom C D} → π₁ ∘ (f ⁂ g) ≡ f ∘ π₁
  π₁∘⁂ {f = f} {g} = commute₁

  .π₂∘⁂ : ∀ {A B C D} → {f : Hom A B} → {g : Hom C D} → π₂ ∘ (f ⁂ g) ≡ g ∘ π₂
  π₂∘⁂ {f = f} {g} = commute₂

  .⁂∘⟨⟩ : ∀ {A B C D E} → {f : Hom B C} {f′ : Hom A B} {g : Hom D E} {g′ : Hom A D} → (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ⁂∘⟨⟩ {f = f} {f′} {g} {g′} = IsEquivalence.sym equiv (universal helper₁ helper₂)
    where
    helper₁ : π₁ ∘ ((f ⁂ g) ∘ ⟨ f′ , g′ ⟩) ≡ f ∘ f′
    helper₁ = 
      begin
        π₁ ∘ ((f ⁂ g) ∘ ⟨ f′ , g′ ⟩)
      ≈⟨ sym assoc ⟩
        (π₁ ∘ (f ⁂ g)) ∘ ⟨ f′ , g′ ⟩
      ≈⟨ ∘-resp-≡ˡ π₁∘⁂ ⟩
        (f ∘ π₁) ∘ ⟨ f′ , g′ ⟩
      ≈⟨ assoc ⟩
        f ∘ (π₁ ∘ ⟨ f′ , g′ ⟩)
      ≈⟨ ∘-resp-≡ʳ commute₁ ⟩
        f ∘ f′
      ∎
      where
      open SetoidReasoning hom-setoid
      open IsEquivalence equiv 

    helper₂ : π₂ ∘ ((f ⁂ g) ∘ ⟨ f′ , g′ ⟩) ≡ g ∘ g′
    helper₂ = 
      begin
        π₂ ∘ ((f ⁂ g) ∘ ⟨ f′ , g′ ⟩)
      ≈⟨ sym assoc ⟩
        (π₂ ∘ (f ⁂ g)) ∘ ⟨ f′ , g′ ⟩
      ≈⟨ ∘-resp-≡ˡ π₂∘⁂ ⟩
        (g ∘ π₂) ∘ ⟨ f′ , g′ ⟩
      ≈⟨ assoc ⟩
        g ∘ (π₂ ∘ ⟨ f′ , g′ ⟩)
      ≈⟨ ∘-resp-≡ʳ commute₂ ⟩
        g ∘ g′
      ∎
      where
      open SetoidReasoning hom-setoid
      open IsEquivalence equiv 

  .first∘⟨⟩ : ∀ {A B C D} → {f : Hom B C} {f′ : Hom A B} {g′ : Hom A D} → first f ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ {f = f} {f′} {g′} = 
    begin
      first f ∘ ⟨ f′ , g′ ⟩
    ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ f′ , id ∘ g′ ⟩ 
    ≈⟨ ⟨⟩-cong₂ refl identityˡ ⟩
      ⟨ f ∘ f′ , g′ ⟩
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv 

  .second∘⟨⟩ : ∀ {A B D E} → {f′ : Hom A B} {g : Hom D E} {g′ : Hom A D} → second g ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ {f′ = f′} {g} {g′} = 
    begin
      second g ∘ ⟨ f′ , g′ ⟩
    ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ id ∘ f′ , g ∘ g′ ⟩ 
    ≈⟨ ⟨⟩-cong₂ identityˡ refl ⟩
      ⟨ f′ , g ∘ g′ ⟩
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv 

  .⁂∘⁂ : ∀ {A B C D E F} → {f : Hom B C} → {f′ : Hom A B} {g : Hom E F} {g′ : Hom D E} → (f ⁂ g) ∘ (f′ ⁂ g′) ≡ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂∘⁂ {B = B} {E = E} {f = f} {f′} {g} {g′} = 
    begin
      (f ⁂ g) ∘ (f′ ⁂ g′)
    ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ (f′ ∘ π₁) , g ∘ (g′ ∘ π₂) ⟩
    ≈⟨ sym (⟨⟩-cong₂ assoc assoc) ⟩
      (f ∘ f′) ⁂ (g ∘ g′)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .⟨⟩∘ : ∀ {A B C D} {f : Hom A B} {g : Hom A C} {q : Hom D A} → ⟨ f , g ⟩ ∘ q ≡ ⟨ f ∘ q , g ∘ q ⟩
  ⟨⟩∘ = IsEquivalence.sym equiv (universal 
    (IsEquivalence.trans equiv (IsEquivalence.sym equiv assoc) (∘-resp-≡ˡ commute₁)) 
    (IsEquivalence.trans equiv (IsEquivalence.sym equiv assoc) (∘-resp-≡ˡ commute₂)))

{-
  -- Laws that take too long and too much memory to check, but that I'd like to write in here, to use them to build cartesian monoidal categories later
  .triangle : ∀ {x} → first π₁ ≡ second π₂ ∘ assocˡ
  triangle = 
    begin
      first π₁
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (IsEquivalence.refl equiv) commute₂) ⟩
      ⟨ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym second∘⟨⟩ ⟩
      second π₂ ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


  .pentagon : ∀ {x} → assocˡ ∘ assocˡ ≡ second assocˡ ∘ (assocˡ ∘ first assocˡ)
  pentagon =
    begin
      assocˡ ∘ assocˡ
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc ⟨⟩∘ ⟩
      ⟨ π₁ ∘ (π₁ ∘ assocˡ) , ⟨ (π₂ ∘ π₁) ∘ assocˡ , π₂ ∘ assocˡ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ʳ commute₁) (⟨⟩-cong₂ assoc commute₂) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ (π₁ ∘ assocˡ) , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) (⟨⟩-cong₂ (∘-resp-≡ʳ commute₁) (IsEquivalence.refl equiv)) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      second assocˡ ∘ (assocˡ ∘ first assocˡ)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv
-}