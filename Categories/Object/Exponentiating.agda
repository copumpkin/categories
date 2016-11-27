{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.BinaryProducts

module Categories.Object.Exponentiating {o ℓ e}
    (C : Category o ℓ e)
    (binary : BinaryProducts C)  where

open Category C
open BinaryProducts binary

import Categories.Object.Product
open Categories.Object.Product C

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

open import Categories.Square
open GlueSquares C

import Categories.Object.Exponential
open   Categories.Object.Exponential C
  hiding (repack)
  renaming (λ-distrib to λ-distrib′)

open import Level

record Exponentiating Σ : Set (o ⊔ ℓ ⊔ e) where
    field 
        exponential : ∀{A} → Exponential A Σ
    module Σ↑ (X : Obj) = Exponential (exponential {X})
    
    infixr 6 Σ↑_ Σ²_

    Σ↑_ : Obj → Obj
    Σ↑_ X = Σ↑.B^A X
    
    
    {-
      Γ ; x : A   ⊢ f x : Σ
      ──────────────────────────────────────   λ-abs A f
      Γ           ⊢ (λ (x : A) → f x) : Σ↑ A
     -}
    λ-abs : ∀ {Γ} A → (Γ × A) ⇒ Σ → Γ ⇒ Σ↑ A
    λ-abs {Γ} A f = Σ↑.λg A product f
    
    {-
      ─────────────────────────────   eval
      f : Σ↑ A ; x : A  ⊢ (f x) : Σ
     -}
    eval : {A : Obj} → (Σ↑ A × A) ⇒ Σ
    eval {A} = Σ↑.eval A ∘ repack product (Σ↑.product A)
    
    {-
      x : A     ⊢  f x : B
      ─────────────────────────────────────────   [Σ↑_]
      k : Σ↑ B  ⊢  (λ (x : A) → k (f x)) : Σ↑ A
    -}
    [Σ↑_] : ∀ {A B} → A ⇒ B → Σ↑ B ⇒ Σ↑ A
    [Σ↑_] {A}{B} f = λ-abs A (eval {B} ∘ second f)
    
    Σ²_ : Obj → Obj
    Σ²_ X = Σ↑ (Σ↑ X)
    
    [Σ²_] : ∀ {X Y} → X ⇒ Y → Σ² X ⇒ Σ² Y
    [Σ² f ] = [Σ↑ [Σ↑ f ] ]
    
    flip : ∀ {A B} → A ⇒ Σ↑ B → B ⇒ Σ↑ A
    flip {A}{B} f = λ-abs {B} A (eval {B} ∘ swap ∘ second f)
    
    -- not sure this is the best name... "partial-apply" might be better
    curry : ∀ {X Y} → (Σ↑ (X × Y) × X) ⇒ Σ↑ Y
    curry {X}{Y} = λ-abs Y (eval {X × Y} ∘ assocˡ)
    
    -- some lemmas from Exponential specialized to C's chosen products
    open Equiv
    open HomReasoning
    
    private
      .repack∘first : ∀ {A X}{f : X ⇒ Σ↑ A}
          → repack product (Σ↑.product A) ∘ first f
          ≡ [ product ⇒ Σ↑.product A ]first f
      repack∘first {A} = [ product ⇒ product ⇒ Σ↑.product A ]repack∘⁂
    
    .β : ∀{A X} {g : (X × A) ⇒ Σ}
        → eval {A} ∘ first (λ-abs A g) ≡ g
    β {A}{X}{g} =
      begin
        (Σ↑.eval A ∘ repack product (Σ↑.product A)) ∘ first (Σ↑.λg A product g)
      ↓⟨ pullʳ repack∘first ⟩
        Σ↑.eval A ∘ [ product ⇒ Σ↑.product A ]first (Σ↑.λg A product g)
      ↓⟨ Σ↑.β A product ⟩
        g
      ∎
    
    .λ-unique : ∀{A X} {g : (X × A) ⇒ Σ} {h : X ⇒ Σ↑ A}
        → (eval ∘ first h ≡ g)
        → (h ≡ λ-abs A g)
    λ-unique {A}{X}{g}{h} commutes 
      = Σ↑.λ-unique A product commutes′
      where
      commutes′ : Σ↑.eval A ∘ [ product ⇒ Σ↑.product A ]first h ≡ g
      commutes′ =
        begin
          Σ↑.eval A ∘ [ product ⇒ Σ↑.product A ]first h
        ↑⟨ pullʳ repack∘first ⟩
          (Σ↑.eval A ∘ repack product (Σ↑.product A)) ∘ first h
        ↓⟨ commutes ⟩
          g
        ∎
    .λ-η : ∀ {A X}{f : X ⇒ Σ↑ A }
        → λ-abs A (eval ∘ first f) ≡ f
    λ-η {A}{X}{f} = sym (λ-unique refl)
        
    .λ-cong : ∀{A B : Obj}{f g : (B × A) ⇒ Σ}
        → (f ≡ g)
        → (λ-abs A f ≡ λ-abs A g)
    λ-cong {A} f≡g = Σ↑.λ-cong A product f≡g

    .subst : ∀ {A C D} {f : (D × A) ⇒ Σ} {g : C ⇒ D}
      → λ-abs {D} A f ∘ g
      ≡ λ-abs {C} A (f ∘ first g)
    subst {A} = Σ↑.subst A product product

    .λ-η-id : ∀ {A} → λ-abs A eval ≡ id
    λ-η-id {A} =
      begin
        Σ↑.λg A product (Σ↑.eval A ∘ repack product (Σ↑.product A))
      ↓⟨ Σ↑.λ-cong A product (∘-resp-≡ʳ (repack≡id⁂id product (Σ↑.product A))) ⟩
        Σ↑.λg A product (Σ↑.eval A ∘ [ product ⇒ Σ↑.product A ]first id)
      ↓⟨ Σ↑.η A product ⟩
        id
      ∎
    
    .λ-distrib : ∀ {A B C}{f : A ⇒ B}{g : (C × B) ⇒ Σ}
        → λ-abs A (g ∘ second f)
        ≡ [Σ↑ f ] ∘ λ-abs B g
    λ-distrib {A}{B}{C}{f}{g} =
      begin
        Σ↑.λg A product (g ∘ second f)
      ↓⟨ λ-distrib′ exponential exponential product product product ⟩
          Σ↑.λg A product (Σ↑.eval B ∘ [ product ⇒ Σ↑.product B ]second f)
        ∘ Σ↑.λg B product g
      ↑⟨ λ-cong (pullʳ [ product ⇒ product ⇒ Σ↑.product B ]repack∘⁂) ⟩∘⟨ refl ⟩
          Σ↑.λg A product ((Σ↑.eval B ∘ repack product (Σ↑.product B)) ∘ second f)
        ∘ Σ↑.λg B product g
      ∎

    .flip² : ∀{A B}{f : A ⇒ Σ↑ B} → flip (flip f) ≡ f
    flip² {A}{B}{f} =
      begin
        λ-abs {A} B (eval {A} ∘ swap ∘ second (flip f))
      ↓⟨ λ-cong lem₁ ⟩
        λ-abs {A} B (eval {B} ∘ first f)
      ↓⟨ λ-η ⟩
        f
      ∎
      where
      lem₁ : eval {A} ∘ swap ∘ second (flip f) ≡ eval {B} ∘ first f
      lem₁ = 
        begin
          eval {A} ∘ swap ∘ second (flip f)
        ↑⟨ assoc ⟩
          (eval {A} ∘ swap) ∘ second (flip f)
        ↓⟨ glue β swap∘⁂ ⟩
          eval {B} ∘ (swap ∘ second f) ∘ swap
        ↓⟨ refl ⟩∘⟨ swap∘⁂ ⟩∘⟨ refl ⟩
          eval {B} ∘ (first f ∘ swap) ∘ swap
        ↓⟨ refl ⟩∘⟨ cancelRight swap∘swap ⟩
          eval {B} ∘ first f
        ∎
