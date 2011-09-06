{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

-- small indexed products of specific shapes

module Categories.Object.IndexedProducts {o ℓ e} (C : Category o ℓ e) where

open Category C
-- open Equiv

open import Level

open import Categories.Support.Equivalence using (Setoid; module Setoid)

import Categories.Object.Indexed as IObj
import Categories.Object.IndexedProduct as IProduct
import Categories.Morphism.Indexed as IArrow
import Categories.Morphisms as Morphisms

record IndexedProducts {c q} {Shape : Setoid c q} : Set (o ⊔ ℓ ⊔ e ⊔ c ⊔ q) where
  open IObj C Shape
  open IArrow C Shape
  open IProduct C
  module Fan-Setoid {V} (xs : Dust) = Setoid (fan-setoid V xs)
  open Fan-Setoid using () renaming (_≈_ to _[_≜_])

  field
    product : ∀ {As} → IndexedProduct Shape As

  ∏ : ∀ As → Obj
  ∏ As = IndexedProduct.∏ (product {As})

  -- ×-comm : ∀ {A B} → _≅_ C (A × B) (B × A)
  -- ×-comm = Commutative product product

  -- ×-assoc : ∀ {X Y Z} → _≅_ C (X × (Y × Z)) ((X × Y) × Z)
  -- ×-assoc = Associative product product product product

  -- Convenience!  well, sort of.
  module Product {As} = IndexedProduct {As = As} (product {As = As})
  open Product using (π; π[_]; π-cong; π▹_; uncurry; commute; commute∗; universal; universal∗; g-η; η; uncurry-cong; uncurry-cong∗; uncurry∘)

  -- assocˡ : ∀ {A B C} → (((A × B) × C) ⇒ (A × (B × C)))
  -- assocˡ = _≅_.g C ×-assoc

  -- assocʳ : ∀ {A B C} → ((A × (B × C)) ⇒ ((A × B) × C))
  -- assocʳ = _≅_.f C ×-assoc

  _⋉π : ∀ {As Bs} → (As ∗⇒∗ Bs) → (∏ As ⇒∗ Bs)
  _⋉π {As} {Bs} fs = _⋉_ {Ys = As} {Bs} fs (π {As})

  bundle : ∀ {As Bs} → (As ∗⇒∗ Bs) → (∏ As ⇒ ∏ Bs)
  bundle {As} {Bs} fs = uncurry {Bs} (_⋉π {As} {Bs} fs)

  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  -- first : ∀ {A B C} → (A ⇒ B) → ((A × C) ⇒ (B × C))
  -- first f = f ⁂ id

  -- second : ∀ {A C D} → (C ⇒ D) → ((A × C) ⇒ (A × D))
  -- second g = id ⁂ g

  -- Just to make this more obvious
  .π▹bundle : ∀ {As Bs} {fs : As ∗⇒∗ Bs} → Bs [ π▹ bundle {As} {Bs} fs ≜ _⋉π {As} {Bs} fs ]
  π▹bundle {As} {Bs} {fs = fs} = commute∗ {Bs} (_⋉π {As} {Bs} fs)

  .π∘bundle : ∀ {As Bs} {fs : As ∗⇒∗ Bs} {x} → π[_] {Bs} x ∘ bundle {As} {Bs} fs ≡ (fs ‼ x) ∘ π[_] {As} x
  π∘bundle {As} {Bs} {fs = fs} = commute {Bs} (_⋉π {As} {Bs} fs)

  .bundle∘uncurry : ∀ {A Bs Cs} {fs : Bs ∗⇒∗ Cs} {gs : A ⇒∗ Bs} → bundle {Bs} {Cs} fs ∘ uncurry {Bs} gs ≡ uncurry {Cs} (_⋉_ {Ys = Bs} {Cs} fs gs)
  bundle∘uncurry {Bs = Bs} {Cs} {fs = fs} {gs} = Equiv.sym (universal {Cs} (_⋉_ {Ys = Bs} {Cs} fs gs) helper)
    where
    helper : ∀ {x} → π[_] {Cs} x ∘ (bundle {Bs} {Cs} fs ∘ uncurry {Bs} gs) ≡ (fs ‼ x) ∘ (gs ‼ x)
    helper {x} = 
      begin
        π[_] {Cs} x ∘ (bundle {Bs} {Cs} fs ∘ uncurry {Bs} gs)
      ↑⟨ assoc ⟩
        (π[_] {Cs} x ∘ bundle {Bs} {Cs} fs) ∘ uncurry {Bs} gs
      ↓⟨ ∘-resp-≡ˡ (π∘bundle {Bs} {Cs} {fs = fs}) ⟩
        ((fs ‼ x) ∘ π[_] {Bs} x) ∘ uncurry {Bs} gs
      ↓⟨ assoc ⟩
        (fs ‼ x) ∘ (π[_] {Bs} x ∘ uncurry {Bs} gs)
      ↓⟨ ∘-resp-≡ʳ (commute {Bs} gs) ⟩
        (fs ‼ x) ∘ (gs ‼ x)
      ∎
      where
      open HomReasoning

  {-
  .first∘⟨⟩ : ∀ {A B C D} → {f : B ⇒ C} {f′ : A ⇒ B} {g′ : A ⇒ D} → first f ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ {f = f} {f′} {g′} = 
    begin
      first f ∘ ⟨ f′ , g′ ⟩
    ↓⟨ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ f′ , id ∘ g′ ⟩ 
    ↓⟨ ⟨⟩-cong₂ refl identityˡ ⟩
      ⟨ f ∘ f′ , g′ ⟩
    ∎
    where
    open HomReasoning

  .second∘⟨⟩ : ∀ {A B D E} → {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → second g ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ {f′ = f′} {g} {g′} = 
    begin
      second g ∘ ⟨ f′ , g′ ⟩
    ↓⟨ ⁂∘⟨⟩ ⟩
      ⟨ id ∘ f′ , g ∘ g′ ⟩ 
    ↓⟨ ⟨⟩-cong₂ identityˡ refl ⟩
      ⟨ f′ , g ∘ g′ ⟩
    ∎
    where
    open HomReasoning
  -}

  .bundle∘bundle : ∀ {As Bs Cs} → {fs : Bs ∗⇒∗ Cs} {gs : As ∗⇒∗ Bs} → (bundle {Bs} {Cs} fs) ∘ (bundle {As} {Bs} gs) ≡ bundle {As} {Cs} (_◽_ {As} {Bs} {Cs} fs gs)
  bundle∘bundle {As} {Bs} {Cs} {fs = fs} {gs} = 
    begin
      (bundle {Bs} {Cs} fs) ∘ (bundle {As} {Bs} gs)
    ↓⟨ bundle∘uncurry {Bs = Bs} {Cs} {fs = fs} ⟩
      uncurry {Cs} (_⋉_ {Ys = Bs} {Cs} fs (_⋉_ {Ys = As} {Bs} gs (π {As})))
    ↑⟨ uncurry-cong∗ {Cs} {_} {_⋉_ {Ys = As} {Cs} (_◽_ {As} {Bs} {Cs} fs gs) (π {As})} {_⋉_ {Ys = Bs} {Cs} fs (_⋉_ {Ys = As} {Bs} gs (π {As}))} (assoc-◽⋉ {Ys = As} {Bs} {Cs} {fs} {gs} {π {As}}) ⟩
      (bundle {As} {Cs} (_◽_ {As} {Bs} {Cs} fs gs))
    ∎
    where
    open HomReasoning
