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
  { unit    = unit
  ; counit  = counit
  ; zig     = zig-zag
  ; zag     = zig-zag
  } where
    Σ² : Obj → Obj
    Σ² X = Σ↑ (Σ↑ X)
    
    [Σ²_] : ∀ {X Y} → X ⇒ Y → Σ² X ⇒ Σ² Y
    [Σ² f ] = [Σ↑ [Σ↑ f ] ]
    
    unit-η : ∀ X → X ⇒ Σ² X
    unit-η _ = flip id
    
    -- TODO: shoot self, then clean up this mess.
    -- Or some permutation thereof.
    -- Don't forget to annotate evals with their types.
    .lem₁ : ∀ {X Y}{f : X ⇒ Y}
      → eval ∘ first (flip id ∘ f)
      ≡ eval ∘ swap ∘ second [Σ↑ f ]
    lem₁ {X}{Y}{f} =
      begin
        eval ∘ first (λ-abs (Σ↑ Y) (eval ∘ swap ∘ second id) ∘ f)
      ↑⟨ refl ⟩∘⟨ first∘first ⟩
        eval 
          ∘ first (λ-abs (Σ↑ Y) (eval ∘ swap ∘ second id))
          ∘ first f
      ↑⟨ assoc ⟩
        (eval ∘ first (λ-abs (Σ↑ Y) (eval ∘ swap ∘ second id)))
          ∘ first f
      ↓⟨ commutes _ ⟩∘⟨ refl ⟩
        (eval ∘ swap ∘ second id) ∘ first f
      ↓⟨ (refl ⟩∘⟨ refl ⟩∘⟨ second-id product) ⟩∘⟨ refl ⟩
        (eval ∘ swap ∘ id) ∘ first f
      ↓⟨ (refl ⟩∘⟨ identityʳ) ⟩∘⟨ refl ⟩
        (eval ∘ swap) ∘ first f
      ↓⟨ assoc ⟩
        eval ∘ swap ∘ first f
      ↓⟨ refl ⟩∘⟨ swap∘⁂ ⟩
        eval ∘ second f ∘ swap
      ↑⟨ assoc ⟩
        (eval ∘ second f) ∘ swap
      ↑⟨ commutes X ⟩∘⟨ refl ⟩
        (eval ∘ first (λ-abs X (eval ∘ second f))) ∘ swap
      ↓⟨ assoc ⟩
        eval ∘ first (λ-abs X (eval ∘ second f)) ∘ swap
      ↑⟨ refl ⟩∘⟨ swap∘⁂ ⟩
        eval ∘ swap ∘ second (λ-abs X (eval ∘ second f))
      ∎
    
    .lem₂ : ∀{X Y} {f : X ⇒ Σ↑ Y}
      → (eval ∘ swap ∘ second id) ∘ second f
      ≡ eval ∘ swap ∘ second f
    lem₂ {X}{Y}{f} =
      begin
        (eval ∘ swap ∘ second id) ∘ second f
      ↓⟨ assoc ⟩
        eval ∘ (swap ∘ second id) ∘ second f
      ↓⟨ refl ⟩∘⟨ assoc ⟩
        eval ∘ swap ∘ second id ∘ second f
      ↓⟨ refl ⟩∘⟨ refl ⟩∘⟨ second∘second ⟩
        eval ∘ swap ∘ second (id ∘ f)
      ↓⟨ refl ⟩∘⟨ refl ⟩∘⟨ ⁂-cong₂ refl identityˡ ⟩
        eval ∘ swap ∘ second f
      ∎
    
    -- [Σ↑ f ] = λ-abs _ (eval ∘ second f)
    .unit-commute : ∀ {X Y} (f : X ⇒ Y)
      → flip id ∘ f ≡ [Σ² f ] ∘ flip id
    unit-commute {X}{Y} f =
      begin
        flip id ∘ f
      ↓⟨ λ-unique (Σ↑ Y) lem₁ ⟩
        flip [Σ↑ f ]
      ↑⟨ λ-resp-≡ (Σ↑ Y) lem₂ ⟩
        λ-abs (Σ↑ Y) ((eval ∘ swap ∘ second id) ∘ second [Σ↑ f ])
      ↑⟨ λ-distrib (Σ↑ Y) ⟩
        [Σ↑ [Σ↑ f ] ] ∘ flip id
      ∎
    
    .counit-commute : ∀ {X Y} (f : X ⇒ Y)
      → [Σ² f ] ∘ flip id ≡ flip id ∘ f
    counit-commute f = sym (unit-commute f)
    
    unit : NaturalTransformation idF Σ²-Functor
    unit = record
      { η       = unit-η
      ; commute = unit-commute
      }
    
    counit : NaturalTransformation (Functor.op Σ²-Functor) idF
    counit = record
      { η       = unit-η
      ; commute = counit-commute
      }
    
    module unit   = NaturalTransformation unit
    module counit = NaturalTransformation counit
    
    F = Functor.op Σ↑-Functor
    G = Σ↑-Functor
    
    .zig-zag : ∀{X}
      → id ≡ [Σ↑ unit.η X ] ∘ unit.η (Σ↑ X)
    zig-zag {X} =
      begin
        id
      ↑⟨ flip² ⟩
        flip (flip id)
      ↑⟨ λ-resp-≡ X lem₂ ⟩
        λ-abs X ((eval ∘ swap ∘ second id) ∘ second (flip id))
      ↑⟨ λ-distrib X ⟩
        [Σ↑ flip id ] ∘ flip id
      ∎

Σ²-Monad : Monad C
Σ²-Monad = Adjunction.monad Σ↑-Self-Adjunction
