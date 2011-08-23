{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Data.Product using (∃)
open import Level

import Categories.Object.Product
open Categories.Object.Product C using (Product)
module Product = Categories.Object.Product.Product C

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    -- TODO: consider re-generalizing this to case where A does not
    -- have all products.  λg is then only defined when there is a product
    -- X × A, and the laws get harder to express because (I think) they
    -- need a more-or-less inline version of 'first' parameterized over
    -- the input product.
    product : ∀ {X} → Product X A

  _×A : Obj → Obj
  _×A X = Product.A×B (product {X})
  
  -- can't just open product because we want X to stay implicit
  ⟨_,_⟩ : ∀ {X Y} → (X ⇒ Y) → (X ⇒ A) → X ⇒ (Y ×A)
  ⟨_,_⟩ = Product.⟨_,_⟩ product
  
  π₁ : ∀{X} → (X ×A) ⇒ X
  π₁ = Product.π₁ product
  
  π₂ : ∀{X} → (X ×A) ⇒ A
  π₂ = Product.π₂ product
  
  first : {X Y : Obj} → (X ⇒ Y) → (X ×A ⇒ Y ×A)
  first f = ⟨ f ∘ π₁ , π₂ ⟩

  field
    eval : B^A ×A ⇒ B
    λg : (X : Obj) → (X ×A ⇒ B) → (X ⇒ B^A)
    .commutes
        : ∀{X}{g : X ×A ⇒ B}
        → (eval ∘ first (λg X g) ≡ g)
    .λ-unique
        : ∀ {X}{g : X ×A ⇒ B}{h : X ⇒ B^A}
        → (eval ∘ first h ≡ g)
        → (h ≡ λg X g)
  
  .identity
      : ∀ {X}{f : X ⇒ B^A }
      → λg X (eval ∘ first f) ≡ f
  identity {X}{f} = sym (λ-unique refl)
    where open Equiv

  .λ-resp-≡
      : ∀ {X f g}
      → (f ≡ g)
      → (λg X f ≡ λg X g)
  λ-resp-≡ {X}{f}{g} f≡g =
    begin
        λg X f
    ↓⟨ λ-unique commutes₂ ⟩
        λg X g
    ∎
    where
        open HomReasoning
        commutes₂ : eval ∘ first (λg X f) ≡ g
        commutes₂ =
            begin
                eval ∘ first (λg X f)
            ↓⟨ commutes ⟩
                f
            ↓⟨ f≡g ⟩
                g
            ∎
