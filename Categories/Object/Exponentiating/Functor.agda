{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.BinaryProducts
open import Categories.Object.Exponentiating

module Categories.Object.Exponentiating.Functor {o a}
    (C : Category o a)
    (binary : BinaryProducts C)
    (Σ : Category.Obj C)
    (exponentiating : Exponentiating C binary Σ) where

open Category C
open BinaryProducts C binary
open Exponentiating C binary exponentiating

open Equiv
open HomReasoning

import Categories.Object.Product.Morphisms
open Categories.Object.Product.Morphisms C

open import Categories.Operations
open import Categories.Functor
  using (Functor-composes; Functor; Contravariant)

Σ↑-Functor : Contravariant C C
Σ↑-Functor = record
    { F₀            =  Σ↑_
    ; F₁            = [Σ↑_]
    ; identity      = identity
    ; homomorphism  = homomorphism
    }
    where
        .identity : ∀ {A} → [Σ↑ id {A} ] ≡ id
        identity {A} = 
            begin
                λ-abs A (eval ∘ second id)
            ↓⟨ λ-cong (∘-resp-≡ refl (id⁂id product)) ⟩
                λ-abs A (eval ∘ id)
            ↓⟨ λ-cong identityʳ ⟩
                λ-abs A eval
            ↓⟨ λ-η-id ⟩
                id
            ∎
        
        .homomorphism : ∀ {X Y Z}
            {f : X ⇒ Y} {g : Y ⇒ Z}
            → [Σ↑ (g ∘ f) ] ≡ [Σ↑ f ] ∘ [Σ↑ g ]
        homomorphism {X}{Y}{Z}{f}{g} =
            begin
                λ-abs X (eval ∘ second (g ∘ f))
            ↑⟨ λ-cong (refl ⟩∘⟨ second∘second) ⟩
                λ-abs X (eval ∘ second g ∘ second f)
            ↑⟨ λ-cong assoc  ⟩
                λ-abs X ((eval ∘ second g) ∘ second f)
            ↓⟨ λ-distrib ⟩
                λ-abs X (eval ∘ second f) 
                    ∘
                λ-abs Y (eval ∘ second g)
            ∎

Σ²-Functor : Functor C C
Σ²-Functor = Σ↑-Functor ∘ Functor.op Σ↑-Functor
