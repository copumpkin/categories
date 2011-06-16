{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Cartesian.Pentagon where

open import Categories.Support.PropositionalEquality using (_≣_; ≣-refl)
open import Categories.Category using (Category; module Category)
open import Categories.Object.BinaryProducts using (BinaryProducts)
open import Categories.Object.BinaryProducts.Abstract
open import Categories.Square

module Law {o ℓ e} (C : Category o ℓ e) (P : BinaryProducts C) where
  open Category C
  open AbstractBinaryProducts C P

  .π₁∘assocˡ : ∀ {X Y Z} → π₁ ∘ assocˡ {X} {Y} {Z} ≡ π₁ ∘ π₁
  π₁∘assocˡ =
    begin
      π₁ ∘ assocˡ
    ↓⟨ ∘-resp-≡ʳ (reflexive assocˡ-convert) ⟩
      π₁ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↓⟨ commute₁ ⟩
      π₁ ∘ π₁
    ∎
    where
    open HomReasoning {_} {_}
    open Equiv using (reflexive)

  abstract
    shave3ˡ : ∀ {A B C} → ((A × B) × C) ⇒ (B × C)
    shave3ˡ = ⟨ π₂ ∘ π₁ , π₂ ⟩ -- in real life, 'first π₂'

    shave3ˡ-convert : ∀ {X Y Z} → shave3ˡ {X} {Y} {Z} ≣ ⟨ π₂ ∘ π₁ , π₂ ⟩
    shave3ˡ-convert = ≣-refl

    .π₁∘shave3ˡ : ∀ {X Y Z} → π₁ ∘ shave3ˡ {X} {Y} {Z} ≡ π₂ ∘ π₁
    π₁∘shave3ˡ = commute₁

    .π₂∘shave3ˡ : ∀ {X Y Z} → π₂ ∘ shave3ˡ {X} {Y} {Z} ≡ π₂
    π₂∘shave3ˡ = commute₂

    assocˡ-convert₂ : ∀ {X Y Z} → assocˡ {X} {Y} {Z} ≣ ⟨ π₁ ∘ π₁ , shave3ˡ ⟩
    assocˡ-convert₂ = assocˡ-convert


  .π₂∘assocˡ : ∀ {X Y Z} → π₂ ∘ assocˡ {X} {Y} {Z} ≡ shave3ˡ
  π₂∘assocˡ =
    begin
      π₂ ∘ assocˡ
    ↓⟨ ∘-resp-≡ʳ (reflexive assocˡ-convert₂) ⟩
      π₂ ∘ ⟨ π₁ ∘ π₁ , shave3ˡ ⟩
    ↓⟨ commute₂ ⟩
      shave3ˡ
    ∎
    where
    open HomReasoning {_} {_}
    open Equiv using (reflexive)

  .π₁₁-assocˡ : ∀ {X Y Z W} → (π₁ ∘ π₁) ∘ assocˡ {_} {Z} {W} ≡ (π₁ ∘ π₁) ∘ first (assocˡ {X} {Y} {Z})
  π₁₁-assocˡ = 
    begin
      (π₁ ∘ π₁) ∘ assocˡ
    ↓⟨ glue (sym π₁∘assocˡ) π₁∘assocˡ ⟩
      π₁ ∘ (assocˡ ∘ π₁)
    ↑⟨ ∘-resp-≡ʳ π₁∘⁂ ⟩
      π₁ ∘ (π₁ ∘ first assocˡ)
    ↑⟨ assoc ⟩
      (π₁ ∘ π₁) ∘ first assocˡ
    ∎
    where
    open HomReasoning {_} {_}
    open Equiv
    open GlueSquares C

  .π₂₁-assocˡ : ∀ {X Y Z W} → (π₂ ∘ π₁) ∘ assocˡ {X × Y} {Z} {W} ≡ (π₂ ∘ π₁) ∘ π₁
  π₂₁-assocˡ =
    begin
      (π₂ ∘ π₁) ∘ assocˡ
    ↓⟨ assoc ⟩
      π₂ ∘ (π₁ ∘ assocˡ)
    ↓⟨ ∘-resp-≡ʳ π₁∘assocˡ ⟩
      π₂ ∘ (π₁ ∘ π₁)
    ↑⟨ assoc ⟩
      (π₂ ∘ π₁) ∘ π₁
    ∎
    where
    open HomReasoning {_} {_}

  abstract
    shave4ˡʳ : ∀ {A B C D} → (((A × B) × C) × D) ⇒ (B × C)
    shave4ˡʳ = ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩

    .shave4ˡʳ-convert : ∀ {A B C D} → shave4ˡʳ {A} {B} {C} {D} ≣ ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩
    shave4ˡʳ-convert = ≣-refl

    .π₁∘shave4ˡʳ : ∀ {A B C D} → π₁ ∘ shave4ˡʳ {A} {B} {C} {D} ≡ (π₂ ∘ π₁) ∘ π₁
    π₁∘shave4ˡʳ = commute₁

    .π₂∘shave4ˡʳ : ∀ {A B C D} → π₂ ∘ shave4ˡʳ {A} {B} {C} {D} ≡ π₂ ∘ π₁
    π₂∘shave4ˡʳ = commute₂

    .shave3ˡ∘π₁ : ∀ {A B C D} → shave3ˡ ∘ π₁ ≡ shave4ˡʳ {A} {B} {C} {D}
    shave3ˡ∘π₁ =
      begin
        shave3ˡ ∘ π₁
      ↓⟨ ∘-resp-≡ˡ (reflexive shave3ˡ-convert) ⟩
        ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ π₁
      ↓⟨ ⟨⟩∘ ⟩
        ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩
      ∎
      where
      open HomReasoning {_} {_}
      open Equiv using (reflexive)
 
  abstract
    shave4ˡ : ∀ {A B C D} → (((A × B) × C) × D) ⇒ ((B × C) × D)
    shave4ˡ = ⟨ shave4ˡʳ , π₂ ⟩

    .shave4ˡ-convert : ∀ {A B C D} → shave4ˡ {A} {B} {C} {D} ≣ ⟨ shave4ˡʳ , π₂ ⟩
    shave4ˡ-convert = ≣-refl

    .π₁∘shave4ˡ : ∀ {A B C D} → π₁ ∘ shave4ˡ ≡ shave4ˡʳ {A} {B} {C} {D}
    π₁∘shave4ˡ = commute₁

    .π₂∘shave4ˡ : ∀ {A B C D} → π₂ ∘ shave4ˡ {A} {B} {C} {D} ≡ π₂
    π₂∘shave4ˡ = commute₂

  .shave3ˡ∘assocˡ : ∀ {X Y Z W} → shave3ˡ ∘ assocˡ ≡ assocˡ ∘ shave4ˡ {X} {Y} {Z} {W}
  shave3ˡ∘assocˡ =
    begin
      shave3ˡ ∘ assocˡ
    ↓⟨ ∘-resp-≡ˡ (reflexive shave3ˡ-convert) ⟩
      ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ assocˡ , π₂ ∘ assocˡ ⟩
    ↓⟨ ⟨ π₂₁-assocˡ ⟩,⟨ π₂∘assocˡ ⟩ ⟩
      ⟨ (π₂ ∘ π₁) ∘ π₁ , shave3ˡ ⟩
    ↓⟨ ⟨ refl ⟩,⟨ reflexive shave3ˡ-convert ⟩ ⟩
      ⟨ (π₂ ∘ π₁) ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↑⟨ ⟨ π₁∘shave4ˡʳ ⟩,⟨ ⟨ π₂∘shave4ˡʳ ⟩,⟨ refl ⟩ ⟩ ⟩
      ⟨ π₁ ∘ shave4ˡʳ , ⟨ π₂ ∘ shave4ˡʳ , π₂ ⟩ ⟩
    ↑⟨ ⟨ ∘-resp-≡ʳ π₁∘shave4ˡ ⟩,⟨ ⟨ ∘-resp-≡ʳ π₁∘shave4ˡ ⟩,⟨ π₂∘shave4ˡ ⟩ ⟩ ⟩
      ⟨ π₁ ∘ (π₁ ∘ shave4ˡ) , ⟨ π₂ ∘ (π₁ ∘ shave4ˡ) , π₂ ∘ shave4ˡ ⟩ ⟩
    ↑⟨ ⟨ assoc ⟩,⟨ ⟨ assoc ⟩,⟨ refl ⟩ ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ shave4ˡ , ⟨ (π₂ ∘ π₁) ∘ shave4ˡ , π₂ ∘ shave4ˡ ⟩ ⟩
    ↑⟨ ⟨ refl ⟩,⟨ ⟨⟩∘ ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ shave4ˡ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ shave4ˡ ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ shave4ˡ
    ↑⟨ ∘-resp-≡ˡ (reflexive assocˡ-convert) ⟩
      assocˡ ∘ shave4ˡ
    ∎
    where
    open HomReasoningP
    open Equiv

  .shave3ˡ∘first-assocˡ : ∀ {X Y Z W} → shave3ˡ ∘ first assocˡ ≡ shave4ˡ {X} {Y} {Z} {W}
  shave3ˡ∘first-assocˡ =
    begin
      shave3ˡ ∘ first assocˡ
    ↓⟨ ∘-resp-≡ˡ (reflexive shave3ˡ-convert) ⟩
      ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ first assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ first assocˡ , π₂ ∘ first assocˡ ⟩
    ↓⟨ ⟨ glue◃◽ π₂∘assocˡ π₁∘⁂ ⟩,⟨ π₂∘⁂ ⟩ ⟩
      ⟨ shave3ˡ ∘ π₁ , id ∘ π₂ ⟩
    ↓⟨ ⟨ shave3ˡ∘π₁ ⟩,⟨ identityˡ ⟩ ⟩
      ⟨ shave4ˡʳ , π₂ ⟩
    ↑≣⟨ shave4ˡ-convert ⟩
      shave4ˡ
    ∎
    where
    open HomReasoningP
    open Equiv
    open GlueSquares C

  .pentagon : ∀ {X Y Z W} → assocˡ {X} {Y} ∘ assocˡ ≡ second (assocˡ {Y} {Z} {W}) ∘ (assocˡ ∘ first (assocˡ {X}))
  pentagon = 
    begin
      assocˡ ∘ assocˡ
    ↓⟨ ∘-resp-≡ˡ (reflexive assocˡ-convert₂) ⟩
      ⟨ π₁ ∘ π₁ , shave3ˡ ⟩ ∘ assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , shave3ˡ ∘ assocˡ ⟩
    ↓⟨ ⟨ refl ⟩,⟨ shave3ˡ∘assocˡ ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , assocˡ ∘ shave4ˡ ⟩
    ↑⟨ ⟨ sym π₁₁-assocˡ ⟩,⟨ ∘-resp-≡ʳ shave3ˡ∘first-assocˡ ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ first assocˡ , assocˡ ∘ (shave3ˡ ∘ first assocˡ) ⟩
    ↑⟨ ⟨ ∘-resp-≡ˡ identityˡ ⟩,⟨ assoc ⟩ ⟩    
      ⟨ (id ∘ (π₁ ∘ π₁)) ∘ first assocˡ , (assocˡ ∘ shave3ˡ) ∘ first assocˡ ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ (π₁ ∘ π₁) , assocˡ ∘ shave3ˡ ⟩ ∘ first assocˡ
    ↑⟨ ∘-resp-≡ˡ ⁂∘⟨⟩ ⟩
      (second assocˡ ∘ ⟨ π₁ ∘ π₁ , shave3ˡ ⟩) ∘ first assocˡ
    ↑⟨ ∘-resp-≡ˡ (∘-resp-≡ʳ (reflexive assocˡ-convert₂)) ⟩
      (second assocˡ ∘ assocˡ) ∘ first assocˡ
    ↓⟨ assoc ⟩ 
      second assocˡ ∘ (assocˡ ∘ first assocˡ)
    ∎
    where
    open HomReasoningP
    open Equiv