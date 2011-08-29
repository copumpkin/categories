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
    λg : {X : Obj} → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ B^A)
    
    .β
        : {X : Obj} → (X×A : Product X A)
        → {g : Product.A×B X×A ⇒ B}
        → (eval ∘ [ X×A ⇒ product ]first (λg X×A g) ≡ g)
    .λ-unique
        : {X : Obj} → (X×A : Product X A)
        → {g : Product.A×B X×A ⇒ B}
        → {h : X ⇒ B^A}
        → (eval ∘ [ X×A ⇒ product ]first h ≡ g)
        → (h ≡ λg X×A g)
  
  .η
      : ∀ {X : Obj} (X×A : Product X A)
      {f : X ⇒ B^A }
      → λg X×A (eval ∘ [ X×A ⇒ product ]first f) ≡ f
  η X×A {f} = sym (λ-unique X×A refl)
    where open Equiv
  
  .λ-resp-≡
      : {X : Obj}(X×A : Product X A)
      → ∀{f g}
      → (f ≡ g)
      → (λg X×A f ≡ λg X×A g)
  λ-resp-≡ X×A {f}{g} f≡g = λ-unique X×A (trans (β X×A) f≡g)
    where
      open Equiv
  
  .cut : ∀ {C D}
    → (p₂ : Product C A)
    → (p₃ : Product D A)
    → {f : Product.A×B p₃ ⇒ B}{g : C ⇒ D}
    → λg p₃ f ∘ g
    ≡ λg p₂ (f ∘ [ p₂ ⇒ p₃ ]first g)
  cut {C}{D} p₂ p₃ {f}{g} = λ-unique p₂ cut-commutes
    where
    open HomReasoning
    open Equiv
    p₁ = product
    cut-commutes =
      begin
          eval ∘ [ p₂ ⇒ p₁ ]first (λg p₃ f ∘ g)
        ↑⟨ refl ⟩∘⟨ [ p₂ ⇒ p₃ ⇒ p₁ ]first∘first ⟩
          eval 
            ∘ [ p₃ ⇒ p₁ ]first (λg p₃ f)
            ∘ [ p₂ ⇒ p₃ ]first g
        ↑⟨ assoc ⟩
          (eval ∘ [ p₃ ⇒ p₁ ]first (λg p₃ f))
                   ∘ [ p₂ ⇒ p₃ ]first g
        ↓⟨ β p₃ ⟩∘⟨ refl ⟩
          f ∘ [ p₂ ⇒ p₃ ]first g
      ∎
  
  .η-id : λg product eval ≡ id
  η-id =
    begin
      λg product eval
    ↑⟨ identityʳ ⟩
      λg product eval ∘ id
    ↓⟨ cut _ _ ⟩
      λg product (eval ∘ [ product ⇒ product ]first id)
    ↓⟨ η product ⟩
      id
    ∎
    where
    open Equiv
    open HomReasoning

open Morphisms C

-- some aliases to make proof signatures less ugly
[_]eval : ∀{A B}(e₁ : Exponential A B) → Exponential.B^A×A e₁ ⇒ B
[ e₁ ]eval = Exponential.eval e₁

[_]λ : ∀{A B}(e₁ : Exponential A B)
  → {X : Obj} → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ Exponential.B^A e₁)
[ e₁ ]λ = Exponential.λg e₁

.λ-distrib : ∀ {A B C D}
  → (e₁ : Exponential C B)
  → (e₂ : Exponential A B)
  → (p₃ : Product D C)
  → (p₄ : Product D A)
  → (p₅ : Product (Exponential.B^A e₂) C)
  → {f : C ⇒ A}{g : Product.A×B p₄ ⇒ B}
  → [ e₁ ]λ p₃ (g ∘ [ p₃ ⇒ p₄ ]second f)
    ≡ [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f)
    ∘ [ e₂ ]λ p₄ g
λ-distrib {A}{B}{C}{D} e₁ e₂ p₃ p₄ p₅ {f}{g} =
  begin
    [ e₁ ]λ p₃ (g ∘ [ p₃ ⇒ p₄ ]second f)
  ↑⟨ e₁.λ-resp-≡ p₃ eval∘second∘first ⟩
    [ e₁ ]λ p₃ (([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f) ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ p₄ g))
  ↑⟨ e₁.cut p₃ p₅ ⟩
      [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f)
    ∘ [ e₂ ]λ p₄ g
  ∎

  where
  open HomReasoning
  open Equiv
  module e₁ = Exponential e₁
  module e₂ = Exponential e₂
  p₁ = e₁.product
  p₂ = e₂.product
  
  eval∘second∘first =
    begin
      ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f) ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ p₄ g)
    ↓⟨ assoc ⟩
      [ e₂ ]eval
          ∘ [ p₅ ⇒ p₂ ]second f
          ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ p₄ g)
    ↑⟨ refl ⟩∘⟨ [ p₄ ⇒ p₂ , p₃ ⇒ p₅ ]first↔second ⟩
      [ e₂ ]eval
          ∘ [ p₄ ⇒ p₂ ]first ([ e₂ ]λ p₄ g)
          ∘ [ p₃ ⇒ p₄ ]second f
    ↑⟨ assoc ⟩
      ([ e₂ ]eval ∘ [ p₄ ⇒ p₂ ]first ([ e₂ ]λ p₄ g))
                  ∘ [ p₃ ⇒ p₄ ]second f
    ↓⟨ e₂.β p₄ ⟩∘⟨ refl ⟩
      g ∘ [ p₃ ⇒ p₄ ]second f
    ∎

convert : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
convert e₁ e₂ = e₂.λg e₁.product e₁.eval
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
          [ e₁ ]λ p₂ [ e₂ ]eval
        ∘ [ e₂ ]λ p₁ [ e₁ ]eval
      ↓⟨ e₁.λ-resp-≡ p₂ (intro-second e₂) ⟩∘⟨ refl ⟩
          [ e₁ ]λ p₂ ([ e₂ ]eval ∘ [ p₂ ⇒ p₂ ]second id)
        ∘ [ e₂ ]λ p₁ [ e₁ ]eval
      ↑⟨ λ-distrib e₁ e₂ p₁ p₁ p₂ ⟩
          [ e₁ ]λ p₁ ([ e₁ ]eval ∘ [ p₁ ⇒ p₁ ]second id)
      ↑⟨ e₁.λ-resp-≡ p₁ (intro-second e₁) ⟩
          [ e₁ ]λ p₁ [ e₁ ]eval
      ↓⟨ e₁.η-id ⟩
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
