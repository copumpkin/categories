{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.BinaryProducts

module Categories.Object.Exponentiating {o ℓ e}
    (C : Category o ℓ e)
    (binary : BinaryProducts C)  where

open Category C
open BinaryProducts C binary

import Categories.Object.Product
open Categories.Object.Product C

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

import Categories.Object.Exponential
open   Categories.Object.Exponential C
  hiding (convert)
  renaming (λ-distrib to λ-distrib′)

open import Categories.Functor
    using (Contravariant)

open import Level

record Exponentiating Σ : Set (o ⊔ ℓ ⊔ e) where
    field 
        exponential : ∀{A} → Exponential A Σ
    module Σ↑ (X : Obj) = Exponential (exponential {X})
    
    Σ↑_ : Obj → Obj
    Σ↑_ X = Σ↑.B^A X
    
    
    {-
      Γ ; x : A   |- f x : Σ
      ---------------------------------------   λ-abs A f
      Γ           |- (λ (x : A) → f x) : Σ↑ A
     -}
    λ-abs : ∀ {Γ} A → (Γ × A) ⇒ Σ → Γ ⇒ Σ↑ A
    λ-abs {Γ} A f = Σ↑.λg A product f
    
    {-
      
      ------------------------------   eval
      f : Σ↑ A ; x : A  |- (f x) : Σ
     -}
    eval : {A : Obj} → (Σ↑ A × A) ⇒ Σ
    eval {A} = Σ↑.eval A ∘ convert product (Σ↑.product A)
    
    {-
      x : A     |-  f x : B
      ------------------------------------------   [Σ↑_]
      k : Σ↑ B  |-  (λ (x : A) → k (f x)) : Σ↑ A
    -}
    [Σ↑_] : ∀ {A B} → A ⇒ B → Σ↑ B ⇒ Σ↑ A
    [Σ↑_] {A}{B} f = λ-abs A (eval ∘ second f)
    
    flip : ∀ {A B} → A ⇒ Σ↑ B → B ⇒ Σ↑ A
    flip {A}{B} f = λ-abs {B} A (eval {B} ∘ swap ∘ second f)
    
    module Lemmas (A : Obj) where
        -- some lemmas from Exponential specialized to C's chosen products
        module Σ↑A = Σ↑ A
        open Equiv
        open HomReasoning
        
        .convert∘first : ∀ {X}{f : X ⇒ Σ↑ A}
            → convert product Σ↑A.product ∘ first f
            ≡ [ product ⇒ Σ↑A.product ]first f
        convert∘first = [ product ⇒ product ⇒ Σ↑A.product ]convert∘⁂
        
        .commutes : ∀{X} {g : (X × A) ⇒ Σ}
            → eval {A} ∘ first (λ-abs A g) ≡ g
        commutes {X}{g} =
            begin
                (Σ↑A.eval ∘ convert product Σ↑A.product) ∘ first (Σ↑A.λg product g)
            ↓⟨ assoc ⟩
                Σ↑A.eval ∘ convert product Σ↑A.product ∘ first (Σ↑A.λg product g)
            ↓⟨ refl ⟩∘⟨ convert∘first ⟩
                Σ↑A.eval ∘ [ product ⇒ Σ↑A.product ]first (Σ↑A.λg product g)
            ↓⟨ Σ↑A.commutes X product ⟩
                g
            ∎
        

        .λ-unique : ∀{X} {g : (X × A) ⇒ Σ} {h : X ⇒ Σ↑ A}
            → (eval ∘ first h ≡ g)
            → (h ≡ λ-abs A g)
        λ-unique {X}{g}{h} commutes 
            = Σ↑A.λ-unique X product commutes′
            where
                commutes′ : Σ↑A.eval ∘ [ product ⇒ Σ↑A.product ]first h ≡ g
                commutes′ =
                    begin
                        Σ↑A.eval ∘ [ product ⇒ Σ↑A.product ]first h
                    ↑⟨ refl ⟩∘⟨ convert∘first ⟩
                        Σ↑A.eval ∘ convert product Σ↑A.product ∘ first h
                    ↑⟨ assoc ⟩
                        (Σ↑A.eval ∘ convert product Σ↑A.product) ∘ first h
                    ↓⟨ commutes ⟩
                        g
                    ∎

        .λ-η : ∀ {X}{f : X ⇒ Σ↑ A }
            → λ-abs A (eval ∘ first f) ≡ f
        λ-η {X}{f} = sym (λ-unique refl)
        
        .λ-resp-≡ : ∀{B : Obj}{f g : (B × A) ⇒ Σ}
            → (f ≡ g)
            → (λ-abs A f ≡ λ-abs A g)
        λ-resp-≡ {B}{f}{g} f≡g
            = Σ↑A.λ-resp-≡ B product f≡g

        .cut : ∀ {C D} {f : (D × A) ⇒ Σ} {g : C ⇒ D}
          → λ-abs {D} A f ∘ g
          ≡ λ-abs {C} A (f ∘ first g)
        cut = Σ↑A.cut

        .λ-η-id : λ-abs A eval ≡ id
        λ-η-id =
          begin
              Σ↑.λg A product (Σ↑.eval A ∘ convert product (Σ↑.product A))
          ↓⟨ Σ↑A.λ-resp-≡ (Σ↑ A) product (∘-resp-≡ refl (convert≡id⁂id product Σ↑A.product)) ⟩
              Σ↑.λg A product (Σ↑.eval A ∘ [ product ⇒ Σ↑A.product ]first id)
          ↓⟨ Σ↑A.η (Σ↑ A) product ⟩
              id
          ∎
    
        .λ-distrib : ∀ {B C}{f : A ⇒ B}{g : (C × B) ⇒ Σ}
            → λ-abs A (eval ∘ second f) ∘ λ-abs B g ≡ λ-abs A (g ∘ second f)
        λ-distrib {B}{C}{f}{g} =
            begin
                Σ↑A.λg product ((Σ↑.eval B ∘ convert product (Σ↑.product B)) ∘ second f)
                  ∘ Σ↑.λg B product g
            ↓⟨ λ-resp-≡ assoc ⟩∘⟨ refl ⟩
                Σ↑A.λg product (Σ↑.eval B ∘ convert product (Σ↑.product B) ∘ second f)
                  ∘ Σ↑.λg B product g
            ↓⟨ λ-resp-≡ (refl ⟩∘⟨ [ product ⇒ product ⇒ Σ↑.product B ]convert∘⁂) ⟩∘⟨ refl ⟩
                Σ↑A.λg product (Σ↑.eval B ∘ [ product ⇒ Σ↑.product B ]second f)
                  ∘ Σ↑.λg B product g
            ↓⟨ λ-distrib′ exponential exponential product product product ⟩
                Σ↑A.λg product (g ∘ second f)
            ∎

    .flip² : ∀{A B}{f : A ⇒ Σ↑ B} → flip (flip f) ≡ f
    flip² {A}{B}{f} =
      begin
        λ-abs {A} B (eval {A} ∘ swap ∘ second (flip f))
      ↓⟨ λ-resp-≡ B lem₁ ⟩
        λ-abs {A} B (eval {B} ∘ first f)
      ↓⟨ λ-η B ⟩
        f
      ∎
      where
      open Equiv
      open HomReasoning
      open Lemmas
      
      lem₁ : eval {A} ∘ swap ∘ second (flip f) ≡ eval {B} ∘ first f
      lem₁ = 
        begin
          eval {A} ∘ swap ∘ second (flip f)
        ↓⟨ refl ⟩∘⟨ swap∘⁂ ⟩
          eval {A} ∘ first (flip f) ∘ swap
        ↑⟨ assoc ⟩
          (eval {A} ∘ first (flip f)) ∘ swap
        ↓⟨ commutes A ⟩∘⟨ refl ⟩
          (eval {B} ∘ swap ∘ second f) ∘ swap
        ↓⟨ assoc ⟩
          eval {B} ∘ (swap ∘ second f) ∘ swap
        ↓⟨ refl ⟩∘⟨ swap∘⁂ ⟩∘⟨ refl ⟩
          eval {B} ∘ (first f ∘ swap) ∘ swap
        ↓⟨ refl ⟩∘⟨ assoc ⟩
          eval {B} ∘ first f ∘ swap ∘ swap
        ↓⟨ refl ⟩∘⟨ refl ⟩∘⟨ swap∘swap ⟩
          eval {B} ∘ first f ∘ id
        ↓⟨ refl ⟩∘⟨ identityʳ ⟩
          eval {B} ∘ first f
        ∎
