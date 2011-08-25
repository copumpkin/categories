{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

import Categories.Object.Product
open Categories.Object.Product C
  hiding (Unique; convert; convert-Iso)

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

import Categories.Morphisms as Morphisms

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
    ↑⟨ λ-resp-≡ B^A product (∘-resp-≡ refl (first-id product)) ⟩
      λg B^A product (eval ∘ [ product ⇒ product ]first id)
    ↑⟨ λ-unique B^A product refl ⟩
      id
    ∎
    where
    open Equiv
    open HomReasoning

open Morphisms C

[_]eval : ∀{A B}(e₁ : Exponential A B) → Exponential.B^A×A e₁ ⇒ B
[ e₁ ]eval = Exponential.eval e₁

[_]λ : ∀{A B}(e₁ : Exponential A B)
  → (X : Obj) → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ Exponential.B^A e₁)
[ e₁ ]λ = Exponential.λg e₁

.λ-distrib : ∀ {A B C D}
  → (e₁ : Exponential C B)
  → (e₂ : Exponential A B)
  → (p₃ : Product D C)
  → (p₄ : Product D A)
  → (p₅ : Product (Exponential.B^A e₂) C)
  → {f : C ⇒ A}{g : Product.A×B p₄ ⇒ B}
  →   [ e₁ ]λ (Exponential.B^A e₂) p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f)
    ∘ [ e₂ ]λ D p₄ g
    ≡ [ e₁ ]λ D p₃ (g ∘ [ p₃ ⇒ p₄ ]second f)
λ-distrib {A}{B}{C}{D} e₁ e₂ p₃ p₄ p₅ {f}{g} =
  e₁.λ-unique D p₃ lem₁
  where
  open HomReasoning
  open Equiv
  module e₁ = Exponential e₁
  module e₂ = Exponential e₂
  p₁ = e₁.product
  p₂ = e₂.product
  
  lem₁ =
    begin
      e₁.eval ∘ [ p₃ ⇒ p₁ ]first
           ([ e₁ ]λ e₂.B^A p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]second f)
          ∘ [ e₂ ]λ D p₄ g)
    ↑⟨ refl ⟩∘⟨ [ p₃ ⇒ p₅ ⇒ p₁ ]first∘first ⟩
      e₁.eval 
        ∘ [ p₅ ⇒ p₁ ]first ([ e₁ ]λ e₂.B^A p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]second f))
        ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ D p₄ g)
    ↑⟨ assoc ⟩
      (e₁.eval ∘ [ p₅ ⇒ p₁ ]first ([ e₁ ]λ e₂.B^A p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]second f)))
               ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ D p₄ g)
    ↓⟨ e₁.commutes e₂.B^A p₅ ⟩∘⟨ refl ⟩
      ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]second f)
                  ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ D p₄ g)
    ↓⟨ assoc ⟩
      [ e₂ ]eval
          ∘ [ p₅ ⇒ p₂ ]second f
          ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ D p₄ g)
    ↑⟨ refl ⟩∘⟨ [ p₃ ⇒ p₅ , p₄ ⇒ p₂ ]first↔second ⟩
      [ e₂ ]eval
          ∘ [ p₄ ⇒ p₂ ]first ([ e₂ ]λ D p₄ g)
          ∘ [ p₃ ⇒ p₄ ]second f
    ↑⟨ assoc ⟩
      ([ e₂ ]eval ∘ [ p₄ ⇒ p₂ ]first ([ e₂ ]λ D p₄ g))
                  ∘ [ p₃ ⇒ p₄ ]second f
    ↓⟨ e₂.commutes D p₄ ⟩∘⟨ refl ⟩
      g ∘ [ p₃ ⇒ p₄ ]second f
    ∎

convert : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
convert e₁ e₂ = e₂.λg e₁.B^A e₁.product e₁.eval
  where
    module e₁ = Exponential e₁
    module e₂ = Exponential e₂

convert-Iso : ∀{A B} (e₁ e₂ : Exponential A B) → Iso (convert e₁ e₂) (convert e₂ e₁)
convert-Iso e₁ e₂ = record
  { isoˡ = iso e₁ e₂
  ; isoʳ = iso e₂ e₁
  }
  where
    open Equiv
    open HomReasoning
    
    .iso : ∀{A B} (e₁ e₂ : Exponential A B) → convert e₂ e₁ ∘ convert e₁ e₂ ≡ id
    iso e₁ e₂ =
      begin
          [ e₁ ]λ e₂.B^A p₂ [ e₂ ]eval
        ∘ [ e₂ ]λ e₁.B^A p₁ [ e₁ ]eval
      ↓⟨ e₁.λ-resp-≡ e₂.B^A p₂ (intro-second e₂) ⟩∘⟨ refl ⟩
          [ e₁ ]λ e₂.B^A p₂ ([ e₂ ]eval ∘ [ p₂ ⇒ p₂ ]second id)
        ∘ [ e₂ ]λ e₁.B^A p₁ [ e₁ ]eval
      ↓⟨ λ-distrib e₁ e₂ p₁ p₁ p₂ ⟩
          [ e₁ ]λ e₁.B^A p₁ ([ e₁ ]eval ∘ [ p₁ ⇒ p₁ ]second id)
      ↑⟨ e₁.λ-resp-≡ e₁.B^A p₁ (intro-second e₁) ⟩
          [ e₁ ]λ e₁.B^A p₁ [ e₁ ]eval
      ↓⟨ e₁.η ⟩
        id
      ∎
      where
        module e₁ = Exponential e₁
        module e₂ = Exponential e₂
        p₁ = e₁.product
        p₂ = e₂.product
        
        intro-second : ∀ {X Y} → (e : Exponential X Y) → _
        intro-second e =
          begin
              [ e ]eval
          ↑⟨ identityʳ ⟩
              [ e ]eval ∘ id
          ↑⟨ refl ⟩∘⟨ second-id p ⟩
              [ e ]eval ∘ [ p ⇒ p ]second id
          ∎ where p = Exponential.product e

Unique : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ≅ Exponential.B^A e₂
Unique e₁ e₂ = record
  { f = convert e₁ e₂
  ; g = convert e₂ e₁
  ; iso = convert-Iso e₁ e₂
  }
