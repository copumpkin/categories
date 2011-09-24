{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Object.Products.Properties {o ℓ e} 
  (C : Category o ℓ e) where

open Category C

open import Level

import Categories.Object.Terminal
open Categories.Object.Terminal C

import Categories.Object.BinaryProducts
open Categories.Object.BinaryProducts C

import Categories.Object.Products
open Categories.Object.Products C

import Categories.Morphisms
open Categories.Morphisms C

module Properties (P : Products) where
  open Products P
  
  open Terminal terminal
  open BinaryProducts binary
  open HomReasoning
  open Equiv
  
  unitˡ : ∀ {X} → (⊤ × X) ≅ X
  unitˡ {X} = record
    { f = π₂
    ; g = ⟨ ! , id {X} ⟩
    ; iso = record
      { isoˡ = 
        begin
          ⟨ ! , id {X} ⟩ ∘ π₂
        ↓⟨ ⟨⟩∘ ⟩
          ⟨ ! ∘ π₂ , id ∘ π₂ ⟩
        ↓⟨ ⟨⟩-cong₂ (!-unique₂ (! ∘ π₂) π₁) (identityˡ) ⟩
          ⟨ π₁ , π₂ ⟩
        ↓⟨ η ⟩
          id
        ∎
      ; isoʳ = commute₂
      }
    }
  
  .unitˡ-natural : ∀ {X Y} {f : X ⇒ Y} → ⟨ ! , id {Y} ⟩ ∘ f ≡ second f ∘ ⟨ ! , id {X} ⟩
  unitˡ-natural {f = f} = 
    begin
      ⟨ ! , id ⟩ ∘ f
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ ! ∘ f , id ∘ f ⟩
    ↑⟨ ⟨⟩-cong₂ (!-unique (! ∘ f)) (id-comm {f = f}) ⟩
      ⟨ ! , f ∘ id ⟩
    ↑⟨ second∘⟨⟩ ⟩
      second f ∘ ⟨ ! , id ⟩
    ∎ 
  
  unitʳ : ∀ {X} → (X × ⊤) ≅ X
  unitʳ {X} = record
    { f = π₁
    ; g = ⟨ id {X} , ! ⟩
    ; iso = record
      { isoˡ = 
        begin
          ⟨ id {X} , ! ⟩ ∘ π₁
        ↓⟨ ⟨⟩∘ ⟩
          ⟨ id ∘ π₁ , ! ∘ π₁ ⟩
        ↓⟨ ⟨⟩-cong₂ (identityˡ) (!-unique₂ (! ∘ π₁) π₂)  ⟩
          ⟨ π₁ , π₂ ⟩
        ↓⟨ η ⟩
          id
        ∎
      ; isoʳ = commute₁
      }
    }
  
  .unitʳ-natural : ∀ {X Y} {f : X ⇒ Y} → ⟨ id , ! ⟩ ∘ f ≡ first f ∘ ⟨ id , ! ⟩
  unitʳ-natural {f = f} =
    begin
      ⟨ id , ! ⟩ ∘ f
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ f , ! ∘ f ⟩
    ↑⟨ ⟨⟩-cong₂ (id-comm {f = f}) (!-unique (! ∘ f)) ⟩
      ⟨ f ∘ id , ! ⟩
    ↑⟨ first∘⟨⟩ ⟩
      first f ∘ ⟨ id , ! ⟩
    ∎
