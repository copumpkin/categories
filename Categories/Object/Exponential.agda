{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Data.Product using (∃)
open import Level

import Categories.Object.Product
open Categories.Object.Product C using (Product; [_⇒_]first; [_⇒_]second; first-id≡id; [_⇒_]_⁂_)
module Product = Categories.Object.Product.Product C

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    product : Product B^A A

  B^A×A : Obj
  B^A×A = Product.A×B product
  
  field
    eval : B^A×A ⇒ B
    λg : (X : Obj) → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ B^A)
    
    .commutes
        : (X : Obj) → (X×A : Product X A)
        → {g : Product.A×B X×A ⇒ B}
        → (eval ∘ [ X×A ⇒ product ]first (λg X X×A g) ≡ g)
    .λ-unique
        : (X : Obj) → (X×A : Product X A)
        → {g : Product.A×B X×A ⇒ B}
        → {h : X ⇒ B^A}
        → (eval ∘ [ X×A ⇒ product ]first h ≡ g)
        → (h ≡ λg X X×A g)
  
  .g-η
      : ∀ (X : Obj) (X×A : Product X A)
      {f : X ⇒ B^A }
      → λg X X×A (eval ∘ [ X×A ⇒ product ]first f) ≡ f
  g-η X X×A {f} = sym (λ-unique X X×A refl)
    where open Equiv

  .λ-resp-≡
      : (X : Obj)(X×A : Product X A)
      → ∀{f g}
      → (f ≡ g)
      → (λg X X×A f ≡ λg X X×A g)
  λ-resp-≡ X X×A {f}{g} f≡g =
    begin
        λg X X×A f
    ↓⟨ λ-unique X X×A commutes₂ ⟩
        λg X X×A g
    ∎
    where
        open HomReasoning
        commutes₂ : eval ∘ [ X×A ⇒ product ]first (λg X X×A f) ≡ g
        commutes₂ =
            begin
                eval ∘ [ X×A ⇒ product ]first (λg X X×A f)
            ↓⟨ commutes X X×A ⟩
                f
            ↓⟨ f≡g ⟩
                g
            ∎
  
  .η : λg B^A product eval ≡ id
  η =
    begin
      λg B^A product eval
    ↑⟨ λ-resp-≡ B^A product identityʳ ⟩
      λg B^A product (eval ∘ id)
    ↑⟨ λ-resp-≡ B^A product (∘-resp-≡ refl (first-id≡id product)) ⟩
      λg B^A product (eval ∘ [ product ⇒ product ]first id)
    ↑⟨ λ-unique B^A product refl ⟩
      id
    ∎
    where
    open Equiv
    open HomReasoning
  
