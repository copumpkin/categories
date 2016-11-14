{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Exponential {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Square

import Categories.Object.Product
open Categories.Object.Product C
  hiding (repack; repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

import Categories.Morphisms as Morphisms

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    product : Product B^A A

  module product = Product product

  B^A×A : Obj
  B^A×A = product.A×B
  
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
  
  .λ-cong
      : {X : Obj}(X×A : Product X A)
      → ∀{f g}
      → (f ≡ g)
      → (λg X×A f ≡ λg X×A g)
  λ-cong X×A {f}{g} f≡g = λ-unique X×A (trans (β X×A) f≡g)
    where
      open Equiv
  
  .subst : ∀ {C D}
    → (p₂ : Product C A)
    → (p₃ : Product D A)
    → {f : Product.A×B p₃ ⇒ B}{g : C ⇒ D}
    → λg p₃ f ∘ g
    ≡ λg p₂ (f ∘ [ p₂ ⇒ p₃ ]first g)
  subst {C}{D} p₂ p₃ {f}{g} = λ-unique p₂ subst-commutes
    where
    open HomReasoning
    open Equiv
    subst-commutes =
      let p₁ = product in
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
    ↓⟨ subst _ _ ⟩
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
  ↑⟨ e₁.λ-cong p₃ eval∘second∘first ⟩
    [ e₁ ]λ p₃ (([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f) ∘ [ p₃ ⇒ p₅ ]first ([ e₂ ]λ p₄ g))
  ↑⟨ e₁.subst p₃ p₅ ⟩
      [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]second f)
    ∘ [ e₂ ]λ p₄ g
  ∎

  where
  open HomReasoning
  open Equiv
  module e₁ = Exponential e₁
  module e₂ = Exponential e₂
  
  eval∘second∘first =
    let p₁ = e₁.product in
    let p₂ = e₂.product in
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

repack : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
repack e₁ e₂ = e₂.λg e₁.product e₁.eval
  where
    module e₁ = Exponential e₁
    module e₂ = Exponential e₂

.repack≡id : ∀{A B} (e : Exponential A B) → repack e e ≡ id
repack≡id e = Exponential.η-id e

.repack∘ : ∀{A B} (e₁ e₂ e₃ : Exponential A B) → repack e₂ e₃ ∘ repack e₁ e₂ ≡ repack e₁ e₃
repack∘ {A} {B} e₁ e₂ e₃ =
  let p₁ = product e₁ in
  let p₂ = product e₂ in
  begin
      [ e₃ ]λ p₂ [ e₂ ]eval
    ∘ [ e₂ ]λ p₁ [ e₁ ]eval
  ↓⟨ λ-cong e₃ p₂ (introʳ (second-id p₂)) ⟩∘⟨ refl ⟩
      [ e₃ ]λ p₂ ([ e₂ ]eval ∘ [ p₂ ⇒ p₂ ]second id)
    ∘ [ e₂ ]λ p₁ [ e₁ ]eval
  ↑⟨ λ-distrib e₃ e₂ p₁ p₁ p₂ ⟩
    [ e₃ ]λ p₁ ([ e₁ ]eval ∘ [ p₁ ⇒ p₁ ]second id)
  ↑⟨ λ-cong e₃ p₁ (introʳ (second-id p₁)) ⟩
    [ e₃ ]λ p₁ [ e₁ ]eval
  ∎
  where
    open Equiv
    open Exponential
    open HomReasoning
    open GlueSquares C

.repack-cancel : ∀{A B} (e₁ e₂ : Exponential A B) → repack e₁ e₂ ∘ repack e₂ e₁ ≡ id
repack-cancel e₁ e₂ = Equiv.trans (repack∘ e₂ e₁ e₂) (repack≡id e₂)

up-to-iso : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ≅ Exponential.B^A e₂
up-to-iso e₁ e₂ = record
  { f = repack e₁ e₂
  ; g = repack e₂ e₁
  ; iso = record
    { isoˡ = repack-cancel e₂ e₁
    ; isoʳ = repack-cancel e₁ e₂
    }
  }

transport-by-iso : ∀{A B} (e : Exponential A B) → ∀ {X} → Exponential.B^A e ≅ X → Exponential A B
transport-by-iso e {X} e≅X = record
  { B^A = X
  ; product = X×A
  ; eval = e.eval
  ; λg = λ Y×A y → f ∘ e.λg Y×A y
  ; β = λ Y×A → let open HomReasoning in let open GlueSquares C in let open Equiv in begin
      e.eval ∘ [ Y×A ⇒ X×A ]first (f ∘ e.λg Y×A _)
    ↓⟨ ∘-resp-≡ʳ (e.product.⟨⟩-cong₂ (pullˡ (cancelLeft isoˡ)) (pullˡ identityˡ)) ⟩
      e.eval ∘ [ Y×A ⇒ e.product ]first (e.λg Y×A _)
    ↓⟨ (e.β Y×A) ⟩
      _
    ∎
  ; λ-unique = λ Y×A y → let open GlueSquares C in
    switch-gfˡ e≅X
     (e.λ-unique Y×A
      (Equiv.trans
       (∘-resp-≡ʳ
        (e.product.⟨⟩-cong₂
         assoc
         (Equiv.sym (pullˡ identityˡ))))
      y)) -- look ma i can write lisp in agda  --xplat
  }
  where
  module e = Exponential e
  X×A = Mobile e.product e≅X idⁱ
  open _≅_ e≅X

