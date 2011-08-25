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

open import Categories.Functor
    using (Contravariant)

open import Level

record Exponentiating Σ : Set (o ⊔ ℓ ⊔ e) where
    field 
        exponential : ∀{A} → Exponential A Σ
    module Σ↑ (X : Obj) = Exponential (exponential {X})
    
    Σ↑_ : Obj → Obj
    Σ↑_ X = Σ↑.B^A X
    
    eval : {A : Obj} → (Σ↑ A × A) ⇒ Σ
    eval {A} = Σ↑.eval A ∘ convert product (Σ↑.product A)
    λ-abs : ∀ {Γ} A → (Γ × A) ⇒ Σ → Γ ⇒ Σ↑ A
    λ-abs {Γ} A f = Σ↑.λg A Γ product f
    
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
            → eval ∘ first (λ-abs A g) ≡ g
        commutes {X}{g} =
            begin
                (Σ↑A.eval ∘ convert product Σ↑A.product) ∘ first (Σ↑A.λg X product g)
            ↓⟨ assoc ⟩
                Σ↑A.eval ∘ convert product Σ↑A.product ∘ first (Σ↑A.λg X product g)
            ↓⟨ refl ⟩∘⟨ convert∘first ⟩
                Σ↑A.eval ∘ [ product ⇒ Σ↑A.product ]first (Σ↑A.λg X product g)
            ↓⟨ Σ↑A.commutes X product ⟩
                g
            ∎
        
        .λ-η : λ-abs A eval ≡ id
        λ-η =
            begin
                Σ↑.λg A (Σ↑ A) product (Σ↑.eval A ∘ convert product (Σ↑.product A))
            ↓⟨ Σ↑A.λ-resp-≡ (Σ↑ A) product (∘-resp-≡ refl (convert≡id⁂id product Σ↑A.product)) ⟩
                Σ↑.λg A (Σ↑ A) product (Σ↑.eval A ∘ [ product ⇒ Σ↑A.product ]first id)
            ↓⟨ Σ↑A.g-η (Σ↑ A) product ⟩
                id
            ∎
        
        .λ-g-η
            : ∀ {X}{f : X ⇒ Σ↑ A }
            → λ-abs A (eval ∘ first f) ≡ f
        λ-g-η {X}{f} = 
            begin
                Σ↑A.λg X product ((Σ↑A.eval ∘ convert product (Σ↑.product A)) ∘ first f)
            ↓⟨ Σ↑A.λ-resp-≡ X product assoc ⟩
                Σ↑A.λg X product (Σ↑A.eval ∘ convert product (Σ↑.product A) ∘ first f)
            ↓⟨ Σ↑A.λ-resp-≡ X product (∘-resp-≡ refl convert∘first) ⟩
                Σ↑A.λg X product (Σ↑A.eval ∘ [ product ⇒ Σ↑A.product ]first f)
            ↓⟨ Σ↑A.g-η X product ⟩
                f
            ∎

        .λ-resp-≡
            : ∀{B : Obj}{f g : (B × A) ⇒ Σ}
            → (f ≡ g)
            → (λ-abs A f ≡ λ-abs A g)
        λ-resp-≡ {B}{f}{g} f≡g
            = Σ↑A.λ-resp-≡ B product f≡g
        
        .λ-unique : ∀{X}
            → {g : (X × A) ⇒ Σ}
            → {h : X ⇒ Σ↑ A}
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
    
    -- TODO: backport this into Exponential module (gonna be painful...)
    -- or abandon the minimalist approach to products there
    .λ-∘ : ∀ {A B C}{f : A ⇒ B}{g : (C × B) ⇒ Σ}
        → λ-abs A (eval ∘ second f) ∘ λ-abs B g ≡ λ-abs A (g ∘ second f)
    λ-∘ {A}{B}{C}{f}{g} = λ-unique A lem₂
        where
            open Equiv
            open HomReasoning
            open Lemmas
            
            lem₂ : eval ∘ first (λ-abs A (eval ∘ second f) ∘ λ-abs B g) ≡ g ∘ second f
            lem₂ =
                begin
                    eval ∘ first (λ-abs A (eval ∘ second f) ∘ λ-abs B g)
                ↑⟨ refl ⟩∘⟨ first∘first ⟩
                    eval ∘ first (λ-abs A (eval ∘ second f)) ∘ first (λ-abs B g)
                ↑⟨ assoc ⟩
                    (eval ∘ first (λ-abs A (eval ∘ second f))) ∘ first (λ-abs B g)
                ↓⟨ commutes A ⟩∘⟨ refl ⟩
                    (eval ∘ second f) ∘ first (λ-abs B g)   
                ↓⟨ assoc ⟩
                    eval ∘ second f ∘ first (λ-abs B g)   
                ↑⟨ refl ⟩∘⟨ first↔second ⟩
                    eval ∘ first (λ-abs B g) ∘ second f
                ↑⟨ assoc ⟩
                    (eval ∘ first (λ-abs B g)) ∘ second f
                ↓⟨ commutes B ⟩∘⟨ refl ⟩
                    g ∘ second f
                ∎
    
    {-
      x : A     |-  f x : B
      ------------------------------------------   [Σ↑_]
      k : Σ↑ B  |-  (λ (x : A) → k (f x)) : Σ↑ A
    -}
    [Σ↑_] : ∀ {A B} → A ⇒ B → Σ↑ B ⇒ Σ↑ A
    [Σ↑_] {A}{B} f = λ-abs A (eval ∘ second f)
    
    Σ↑-Functor : Contravariant C C
    Σ↑-Functor = record
        { F₀            =  Σ↑_
        ; F₁            = [Σ↑_]
        ; identity      = identity
        ; homomorphism  = homomorphism
        ; F-resp-≡      = F-resp-≡
        }
        where
            open Equiv
            open HomReasoning
            
            .identity : ∀ {A} → [Σ↑ id {A} ] ≡ id
            identity {A} = 
                begin
                    λ-abs A (eval ∘ second id)
                ↓⟨ λ-resp-≡ (∘-resp-≡ refl (id⁂id product)) ⟩
                    λ-abs A (eval ∘ id)
                ↓⟨ λ-resp-≡ identityʳ ⟩
                    λ-abs A eval
                ↓⟨ λ-η ⟩
                    id
                ∎ where open Lemmas A
            
            .homomorphism : ∀ {X Y Z}
                {f : X ⇒ Y} {g : Y ⇒ Z}
                → [Σ↑ (g ∘ f) ] ≡ [Σ↑ f ] ∘ [Σ↑ g ]
            homomorphism {X}{Y}{Z}{f}{g} =
                begin
                    λ-abs X (eval ∘ second (g ∘ f))
                ↑⟨ λ-resp-≡ (∘-resp-≡ refl second∘second)  ⟩
                    λ-abs X (eval ∘ second g ∘ second f)
                ↑⟨ λ-resp-≡ assoc  ⟩
                    λ-abs X ((eval ∘ second g) ∘ second f)
                ↑⟨ λ-∘ ⟩
                    λ-abs X (eval ∘ second f) 
                        ∘
                    λ-abs Y (eval ∘ second g)
                ∎
                where
                    open Lemmas X
            
            .F-resp-≡ : ∀ {A B}{f g : A ⇒ B }
                → f ≡ g → [Σ↑ f ] ≡ [Σ↑ g ]
            F-resp-≡ {A}{B}{f}{g} f≡g =
                begin
                    λ-abs A (eval ∘ second f)
                ↓⟨ λ-resp-≡ (refl ⟩∘⟨ ⟨⟩-cong₂ refl (f≡g ⟩∘⟨ refl)) ⟩
                    λ-abs A (eval ∘ second g)
                ∎ where open Lemmas A

