{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category
open import Categories.Object.Terminal
open import Level

module Categories.Object.Terminal.Exponentials {o ℓ e : Level}
    (C : Category o ℓ e)
    (T : Terminal C) where

open Category C
open Terminal T

import Categories.Object.Exponential
import Categories.Object.Product
import Categories.Object.Product.Morphisms
import Categories.Object.Terminal.Products

open Categories.Object.Exponential C hiding (repack)
open Categories.Object.Product C
open Categories.Object.Product.Morphisms C
open Categories.Object.Terminal.Products C T

[_↑⊤] : Obj → Obj
[ B ↑⊤] = B

[_↑⊤]-exponential : (B : Obj) → Exponential ⊤ B
[ B ↑⊤]-exponential = record
    { B^A       = [ B ↑⊤]
    ; product   = [ B ×⊤]-product
    ; eval      = id
    ; λg        = λ {X} p g → g ∘ repack [ X ×⊤]-product p
    ; β         = λ {X} p {g} → 
        begin
            id ∘ (g ∘ [ p ]⟨ id , ! ⟩) ∘ [ p ]π₁
        ↓⟨ identityˡ ⟩
            (g ∘ [ p ]⟨ id , ! ⟩) ∘ [ p ]π₁
        ↓⟨ assoc ⟩
            g ∘ [ p ]⟨ id , ! ⟩ ∘ [ p ]π₁
        ↓⟨ refl ⟩∘⟨ Product.⟨⟩∘ p ⟩
            g ∘ [ p ]⟨ id ∘ [ p ]π₁ , ! ∘ [ p ]π₁ ⟩
        ↓⟨ refl ⟩∘⟨ Product.⟨⟩-cong₂ p identityˡ (!-unique₂ (! ∘ [ p ]π₁) [ p ]π₂) ⟩
            g ∘ [ p ]⟨ [ p ]π₁ , [ p ]π₂ ⟩
        ↓⟨ refl ⟩∘⟨ Product.η p ⟩
            g ∘ id
        ↓⟨ identityʳ ⟩
            g
        ∎
    ; λ-unique  = λ{X} p {g}{h} h-commutes → 
        begin
            h
        ↑⟨ identityʳ ⟩
            h ∘ id
        ↑⟨ refl ⟩∘⟨ Product.commute₁ p ⟩
            h ∘ [ p ]π₁ ∘ [ p ]⟨ id , ! ⟩
        ↑⟨ assoc ⟩
            (h ∘ [ p ]π₁) ∘ [ p ]⟨ id , ! ⟩
        ↑⟨ identityˡ ⟩∘⟨ refl ⟩
            (id ∘ h ∘ [ p ]π₁) ∘ [ p ]⟨ id , ! ⟩
        ↓⟨ h-commutes ⟩∘⟨ refl ⟩
            g ∘ repack [ X ×⊤]-product p
        ∎
    } 
    where
    open HomReasoning
    open Equiv

[⊤↑_] : Obj → Obj
[⊤↑ B ] = ⊤

[⊤↑_]-exponential : (A : Obj) → Exponential A ⊤
[⊤↑ A ]-exponential = record
    { B^A       = [⊤↑ A ]
    ; product   = [⊤× A ]-product
    ; eval      = !
    ; λg        = λ _ _ → !
    ; β         = λ _   → !-unique₂ _ _
    ; λ-unique  = λ _ _ → !-unique₂ _ _
    } 
