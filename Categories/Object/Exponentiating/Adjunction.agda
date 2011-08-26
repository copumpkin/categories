{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.BinaryProducts
open import Categories.Object.Exponentiating

module Categories.Object.Exponentiating.Adjunction {o ℓ e}
    (C : Category o ℓ e)
    (binary : BinaryProducts C)
    (Σ : Category.Obj C)
    (exponentiating : Exponentiating C binary Σ) where

open Category C
open BinaryProducts C binary
open Exponentiating C binary exponentiating

import Categories.Object.Product
open Categories.Object.Product C

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

open Equiv
open HomReasoning
open Lemmas

import Categories.Object.Exponentiating.Functor
open Categories.Object.Exponentiating.Functor C binary Σ exponentiating

open import Categories.Functor
  using (Functor; Contravariant)
  renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)

open import Categories.Adjunction
open import Categories.NaturalTransformation
  using (NaturalTransformation; module NaturalTransformation)
open import Categories.Monad
  using (Monad)

Σ↑-Self-Adjunction : Adjunction (Functor.op Σ↑-Functor) Σ↑-Functor
Σ↑-Self-Adjunction = record
  { unit    = record
      { η       = λ _ → flip id
      ; commute = unit-commute
      }
  ; counit  = record
      { η       = λ _ → flip id
      ; commute = counit-commute
      }
  ; zig     = zig-zag
  ; zag     = zig-zag
  } where
    Σ² : Obj → Obj
    Σ² X = Σ↑ (Σ↑ X)
    
    [Σ²_] : ∀ {X Y} → X ⇒ Y → Σ² X ⇒ Σ² Y
    [Σ² f ] = [Σ↑ [Σ↑ f ] ]
    
    .lem₁ : ∀{A B C D}{f : (B × C) ⇒ D}{g : A ⇒ (C × B)}
      → (f ∘ swap ∘ second id) ∘ g
      ≡ f ∘ swap ∘ g
    lem₁ {A}{B}{C}{D}{f}{g} =
      begin
        (f ∘ swap ∘ second id) ∘ g
      ↓⟨ (refl ⟩∘⟨ refl ⟩∘⟨ second-id product) ⟩∘⟨ refl ⟩
        (f ∘ swap ∘ id) ∘ g
      ↓⟨ (refl ⟩∘⟨ identityʳ) ⟩∘⟨ refl ⟩
        (f ∘ swap) ∘ g
      ↓⟨ assoc ⟩
        f ∘ swap ∘ g
      ∎
    
    .lem₂ : ∀ {X Y}{f : X ⇒ Y}
      → eval {Σ↑ Y} ∘ first (flip id ∘ f)
      ≡ eval {X}    ∘ swap ∘ second [Σ↑ f ]
    lem₂ {X}{Y}{f} =
      begin
        eval {Σ↑ Y} ∘ first (flip id ∘ f)
      ↑⟨ refl ⟩∘⟨ first∘first ⟩
        eval {Σ↑ Y} ∘ first (flip id) ∘ first f
      ↑⟨ assoc ⟩
        (eval {Σ↑ Y} ∘ first (flip id)) ∘ first f
      ↓⟨ commutes (Σ↑ Y) ⟩∘⟨ refl ⟩
        (eval {Y} ∘ swap ∘ second id) ∘ first f
      ↓⟨ lem₁ ⟩
        eval {Y} ∘ swap ∘ first f
      ↓⟨ refl ⟩∘⟨ swap∘⁂ ⟩
        eval {Y} ∘ second f ∘ swap
      ↑⟨ assoc ⟩
        (eval {Y} ∘ second f) ∘ swap
      ↑⟨ commutes X ⟩∘⟨ refl ⟩
        (eval {X} ∘ first (λ-abs X (eval {Y} ∘ second f))) ∘ swap
      ↓⟨ assoc ⟩
        eval {X} ∘ first (λ-abs X (eval {Y} ∘ second f)) ∘ swap
      ↑⟨ refl ⟩∘⟨ swap∘⁂ ⟩
        eval {X} ∘ swap ∘ second (λ-abs X (eval ∘ second f))
      ∎
    
    .unit-commute : ∀ {X Y} (f : X ⇒ Y)
      → flip id ∘ f ≡ [Σ² f ] ∘ flip id
    unit-commute {X}{Y} f =
      begin
        flip id ∘ f
      ↓⟨ λ-unique (Σ↑ Y) lem₂ ⟩
        flip [Σ↑ f ]
      ↑⟨ λ-resp-≡ (Σ↑ Y) lem₁ ⟩
        λ-abs (Σ↑ Y) ((eval {X} ∘ swap ∘ second id) ∘ second [Σ↑ f ])
      ↓⟨ λ-distrib (Σ↑ Y) ⟩
        [Σ↑ [Σ↑ f ] ] ∘ flip id
      ∎
    
    .counit-commute : ∀ {X Y} (f : X ⇒ Y)
      → [Σ² f ] ∘ flip id ≡ flip id ∘ f
    counit-commute f = sym (unit-commute f)
    
    .zig-zag : ∀{X}
      → id ≡ [Σ↑ flip id ] ∘ flip id
    zig-zag {X} =
      begin
        id
      ↑⟨ flip² ⟩
        flip (flip id)
      ↑⟨ λ-resp-≡ X lem₁ ⟩
        λ-abs X ((eval ∘ swap ∘ second id) ∘ second (flip id))
      ↓⟨ λ-distrib X ⟩
        [Σ↑ flip id ] ∘ flip id
      ∎

Σ²-Monad : Monad C
Σ²-Monad = Adjunction.monad Σ↑-Self-Adjunction
