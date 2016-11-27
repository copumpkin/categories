{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.BinaryCoproducts {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level

import Categories.Object.Coproduct as Coproduct
open import Categories.Morphisms C

open module CP = Coproduct C hiding (module BinCoproducts)
open CP public using (BinCoproducts)

record BinaryCoproducts : Set (o ⊔ ℓ ⊔ e) where
  infix 10 _⧻_

  field
    coproduct : ∀ {A B} → Coproduct A B

  _∐_ : Obj → Obj → Obj
  A ∐ B = Coproduct.A+B (coproduct {A} {B})

  ∐-comm : ∀ {A B} → _≅_ (A ∐ B) (B ∐ A)
  ∐-comm = Commutative coproduct coproduct

  ∐-assoc : ∀ {X Y Z} → _≅_ (X ∐ (Y ∐ Z)) ((X ∐ Y) ∐ Z)
  ∐-assoc = Associative coproduct coproduct coproduct coproduct

  -- Convenience!
  i₁ : {A B : Obj} → (A ⇒ (A ∐ B))
  i₁ = Coproduct.i₁ coproduct

  i₂ : {A B : Obj} → (B ⇒ (A ∐ B))
  i₂ = Coproduct.i₂ coproduct

  [_,_] : ∀ {A B Q} → (A ⇒ Q) → (B ⇒ Q) → ((A ∐ B) ⇒ Q)
  [_,_] = Coproduct.[_,_] coproduct

  .commute₁ : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} → [ f , g ] ∘ i₁ ≡ f
  commute₁ = Coproduct.commute₁ coproduct

  .commute₂ : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} → [ f , g ] ∘ i₂ ≡ g
  commute₂ = Coproduct.commute₂ coproduct

  .universal : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} {i : (A ∐ B) ⇒ C}
               → i ∘ i₁ ≡ f → i ∘ i₂ ≡ g → [ f , g ] ≡ i
  universal = Coproduct.universal coproduct

  assocˡ : ∀ {A B C} → (((A ∐ B) ∐ C) ⇒ (A ∐ (B ∐ C)))
  assocˡ = _≅_.g ∐-assoc

  assocʳ : ∀ {A B C} → ((A ∐ (B ∐ C)) ⇒ ((A ∐ B) ∐ C))
  assocʳ = _≅_.f ∐-assoc

  .g-η : ∀ {A B C} {f : (A ∐ B) ⇒ C} → [ f ∘ i₁ , f ∘ i₂ ] ≡ f
  g-η = Coproduct.g-η coproduct

  .η : ∀ {A B} → [ i₁ , i₂ ] ≡ id {A ∐ B}
  η = Coproduct.η coproduct

  .[]-cong₂ : ∀ {A B C} → {f f′ : A ⇒ C} {g g′ : B ⇒ C} → f ≡ f′ → g ≡ g′ → [ f , g ] ≡ [ f′ , g′ ]
  []-cong₂ = Coproduct.[]-cong₂ coproduct
  
  -- If I _really_ wanted to, I could do this for a specific pair of coproducts like the rest above, but I'll write that one
  -- when I need it.
  _⧻_ : ∀ {A B C D} → (A ⇒ B) → (C ⇒ D) → ((A ∐ C) ⇒ (B ∐ D))
  f ⧻ g = [ i₁ ∘ f , i₂ ∘ g ]

  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  left : ∀ {A B C} → (A ⇒ B) → ((A ∐ C) ⇒ (B ∐ C))
  left f = f ⧻ id

  right : ∀ {A C D} → (C ⇒ D) → ((A ∐ C) ⇒ (A ∐ D))
  right g = id ⧻ g

  -- Just to make this more obvious
  .⧻∘i₁ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → (f ⧻ g) ∘ i₁ ≡ i₁ ∘ f
  ⧻∘i₁ {f = f} {g} = commute₁

  .⧻∘i₂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} → (f ⧻ g) ∘ i₂ ≡ i₂ ∘ g
  ⧻∘i₂ {f = f} {g} = commute₂

  .[]∘⧻ : ∀ {A B C D E} → {f : B ⇒ E} {f′ : A ⇒ B} {g : D ⇒ E} {g′ : C ⇒ D} → [ f , g ] ∘ ( f′ ⧻ g′ ) ≡ [ f ∘ f′ , g ∘ g′ ]
  []∘⧻ {f = f} {f′} {g} {g′} = sym (universal helper₁ helper₂)
    where
    helper₁ : ([ f , g ] ∘ (f′ ⧻ g′)) ∘ i₁ ≡ f ∘ f′
    helper₁ = 
      begin
        ([ f , g ] ∘ (f′ ⧻ g′)) ∘ i₁
      ↓⟨ assoc ⟩
        [ f , g ] ∘ ((f′ ⧻ g′) ∘ i₁)
      ↓⟨ ∘-resp-≡ʳ ⧻∘i₁ ⟩
        [ f , g ] ∘ (i₁ ∘ f′)
      ↑⟨ assoc ⟩
        ([ f , g ] ∘ i₁) ∘ f′
      ↓⟨ ∘-resp-≡ˡ commute₁ ⟩
        f ∘ f′
      ∎
      where
      open HomReasoning

    helper₂ : ([ f , g ] ∘ (f′ ⧻ g′)) ∘ i₂ ≡ g ∘ g′
    helper₂ = 
      begin
        ([ f , g ] ∘ (f′ ⧻ g′)) ∘ i₂
      ↓⟨ assoc ⟩
        [ f , g ] ∘ ((f′ ⧻ g′) ∘ i₂)
      ↓⟨ ∘-resp-≡ʳ ⧻∘i₂ ⟩
        [ f , g ] ∘ (i₂ ∘ g′)
      ↑⟨ assoc ⟩
        ([ f , g ] ∘ i₂) ∘ g′
      ↓⟨ ∘-resp-≡ˡ commute₂ ⟩
        g ∘ g′
      ∎
      where
      open HomReasoning

  .[]∘left : ∀ {A B C D} → {f : C ⇒ B} {f′ : B ⇒ A} {g′ : D ⇒ A} → [ f′ , g′ ] ∘ left f ≡ [ f′ ∘ f , g′ ]
  []∘left {f = f} {f′} {g′} = 
    begin
      [ f′ , g′ ] ∘ left f
    ↓⟨ []∘⧻ ⟩
      [ f′ ∘ f , g′ ∘ id ] 
    ↓⟨ []-cong₂ refl identityʳ ⟩
      [ f′ ∘ f , g′ ]
    ∎
    where
    open HomReasoning

  .[]∘right : ∀ {A B D E} → {f′ : B ⇒ A} {g : E ⇒ D} {g′ : D ⇒ A} → [ f′ , g′ ] ∘ right g ≡ [ f′ , g′ ∘ g ]
  []∘right {f′ = f′} {g} {g′} = 
    begin
      [ f′ , g′ ] ∘ right g
    ↓⟨ []∘⧻ ⟩
      [ f′ ∘ id , g′ ∘ g ] 
    ↓⟨ []-cong₂ identityʳ refl ⟩
      [ f′ , g′ ∘ g ]
    ∎
    where
    open HomReasoning

  .⧻∘⧻ : ∀ {A B C D E F} → {f : B ⇒ C} → {f′ : A ⇒ B} {g : E ⇒ F} {g′ : D ⇒ E} → (f ⧻ g) ∘ (f′ ⧻ g′) ≡ (f ∘ f′) ⧻ (g ∘ g′)
  ⧻∘⧻ {B = B} {E = E} {f = f} {f′} {g} {g′} = 
    begin
      (f ⧻ g) ∘ (f′ ⧻ g′)
    ↓⟨ []∘⧻ ⟩
      [ (i₁ ∘ f) ∘ f′ , (i₂ ∘ g) ∘ g′ ]
    ↓⟨ []-cong₂ assoc assoc ⟩
      (f ∘ f′) ⧻ (g ∘ g′)
    ∎
    where
    open HomReasoning

  .∘[] : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ A} {q : A ⇒ D} → q ∘ [ f , g ] ≡ [ q ∘ f , q ∘ g ]
  ∘[] = sym (universal (trans assoc (∘-resp-≡ʳ commute₁)) (trans assoc (∘-resp-≡ʳ commute₂)))


Bin→Binary : BinCoproducts -> BinaryCoproducts
Bin→Binary bc = record { coproduct = λ {A} {B} → record {
                                               A+B = A + B;
                                               i₁ = i₁;
                                               i₂ = i₂;
                                               [_,_] = [_,_];
                                               commute₁ = commute₁;
                                               commute₂ = commute₂;
                                               universal = universal } }
  where
    open CP.BinCoproducts bc

