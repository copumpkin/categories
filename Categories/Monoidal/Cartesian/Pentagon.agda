{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Cartesian.Pentagon where

open import Categories.Support.PropositionalEquality using (_≣_; ≣-refl)
open import Categories.Category using (Category; module Category)
open import Categories.Object.BinaryProducts
open import Categories.Square

module Law {o ℓ e} (C : Category o ℓ e) (P : BinaryProducts C) where
  open Category C
  open BinaryProducts P

  shave3ˡ : ∀ {A B C} → ((A × B) × C) ⇒ (B × C)
  shave3ˡ = ⟨ π₂ ∘ π₁ , π₂ ⟩ -- in real life, 'first π₂'

  shave4ˡʳ : ∀ {A B C D} → (((A × B) × C) × D) ⇒ (B × C)
  shave4ˡʳ = ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩

  shave4ˡ : ∀ {A B C D} → (((A × B) × C) × D) ⇒ ((B × C) × D)
  shave4ˡ = ⟨ shave4ˡʳ , π₂ ⟩

  .π₁∘assocˡ : ∀ {X Y Z} → π₁ ∘ assocˡ {X} {Y} {Z} ≡ π₁ ∘ π₁
  π₁∘assocˡ = commute₁

  .π₂∘assocˡ : ∀ {X Y Z} → π₂ ∘ assocˡ {X} {Y} {Z} ≡ shave3ˡ
  π₂∘assocˡ = commute₂
  
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
    open HomReasoning

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
  
  .π₁∘shave4ˡʳ : ∀ {A B C D} → π₁ ∘ shave4ˡʳ {A} {B} {C} {D} ≡ (π₂ ∘ π₁) ∘ π₁
  π₁∘shave4ˡʳ = commute₁
  
  .π₂∘shave4ˡʳ : ∀ {A B C D} → π₂ ∘ shave4ˡʳ {A} {B} {C} {D} ≡ π₂ ∘ π₁
  π₂∘shave4ˡʳ = commute₂

  .shave3ˡ∘π₁ : ∀ {A B C D} → shave3ˡ ∘ π₁ ≡ shave4ˡʳ {A} {B} {C} {D}
  shave3ˡ∘π₁ = ⟨⟩∘

  .π₁∘shave4ˡ : ∀ {A B C D} → π₁ ∘ shave4ˡ ≡ shave4ˡʳ {A} {B} {C} {D}
  π₁∘shave4ˡ = commute₁
  
  .π₂∘shave4ˡ : ∀ {A B C D} → π₂ ∘ shave4ˡ {A} {B} {C} {D} ≡ π₂
  π₂∘shave4ˡ = commute₂
  
  private
    infix 3 ⟨_⟩,⟨_⟩
    .⟨_⟩,⟨_⟩ : ∀ {A B C} → {f f′ : A ⇒ B} {g g′ : A ⇒ C} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
    ⟨_⟩,⟨_⟩ x y = ⟨⟩-cong₂ x y
    
  .shave3ˡ∘assocˡ : ∀ {X Y Z W} → shave3ˡ ∘ assocˡ ≡ assocˡ ∘ shave4ˡ {X} {Y} {Z} {W}
  shave3ˡ∘assocˡ =
    begin
      shave3ˡ ∘ assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ assocˡ , π₂ ∘ assocˡ ⟩
    ↓⟨ ⟨ π₂₁-assocˡ ⟩,⟨ π₂∘assocˡ ⟩ ⟩
      ⟨ (π₂ ∘ π₁) ∘ π₁ , shave3ˡ ⟩
    ↑⟨ ⟨ π₁∘shave4ˡʳ ⟩,⟨ ⟨⟩-congˡ π₂∘shave4ˡʳ ⟩ ⟩
      ⟨ π₁ ∘ shave4ˡʳ , ⟨ π₂ ∘ shave4ˡʳ , π₂ ⟩ ⟩
    ↑⟨ ⟨ ∘-resp-≡ʳ π₁∘shave4ˡ ⟩,⟨ ⟨ ∘-resp-≡ʳ π₁∘shave4ˡ ⟩,⟨ π₂∘shave4ˡ ⟩ ⟩ ⟩
      ⟨ π₁ ∘ (π₁ ∘ shave4ˡ) , ⟨ π₂ ∘ (π₁ ∘ shave4ˡ) , π₂ ∘ shave4ˡ ⟩ ⟩
    ↑⟨ ⟨ assoc ⟩,⟨ ⟨⟩-congˡ assoc ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ shave4ˡ , ⟨ (π₂ ∘ π₁) ∘ shave4ˡ , π₂ ∘ shave4ˡ ⟩ ⟩
    ↑⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ shave4ˡ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ shave4ˡ ⟩
    ↑⟨ ⟨⟩∘ ⟩
      assocˡ ∘ shave4ˡ
    ∎
    where
    open HomReasoning
    open Equiv
  
  .shave3ˡ∘first-assocˡ : ∀ {X Y Z W} → shave3ˡ ∘ first assocˡ ≡ shave4ˡ {X} {Y} {Z} {W}
  shave3ˡ∘first-assocˡ =
    begin
      shave3ˡ ∘ first assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ first assocˡ , π₂ ∘ first assocˡ ⟩
    ↓⟨ ⟨ glue◃◽ π₂∘assocˡ π₁∘⁂ ⟩,⟨ π₂∘⁂ ⟩ ⟩
      ⟨ shave3ˡ ∘ π₁ , id ∘ π₂ ⟩
    ↓⟨ ⟨ shave3ˡ∘π₁ ⟩,⟨ identityˡ ⟩ ⟩
      shave4ˡ
    ∎
    where
    open HomReasoning
    open Equiv
    open GlueSquares C

  .pentagon : ∀ {X Y Z W} → assocˡ {X} {Y} ∘ assocˡ ≡ second (assocˡ {Y} {Z} {W}) ∘ (assocˡ ∘ first (assocˡ {X}))
  pentagon = 
    begin
      assocˡ ∘ assocˡ
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , shave3ˡ ∘ assocˡ ⟩
    ↓⟨ ⟨⟩-congʳ shave3ˡ∘assocˡ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , assocˡ ∘ shave4ˡ ⟩
    ↑⟨ ⟨ sym π₁₁-assocˡ ⟩,⟨ ∘-resp-≡ʳ shave3ˡ∘first-assocˡ ⟩ ⟩
      ⟨ (π₁ ∘ π₁) ∘ first assocˡ , assocˡ ∘ (shave3ˡ ∘ first assocˡ) ⟩
    ↑⟨ ⟨ ∘-resp-≡ˡ identityˡ ⟩,⟨ assoc ⟩ ⟩
      ⟨ (id ∘ (π₁ ∘ π₁)) ∘ first assocˡ , (assocˡ ∘ shave3ˡ) ∘ first assocˡ ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ (π₁ ∘ π₁) , assocˡ ∘ shave3ˡ ⟩ ∘ first assocˡ
    ↑⟨ ∘-resp-≡ˡ ⁂∘⟨⟩ ⟩
      (second assocˡ ∘ assocˡ) ∘ first assocˡ
    ↓⟨ assoc ⟩ 
      second assocˡ ∘ (assocˡ ∘ first assocˡ)
    ∎
    where
    open HomReasoning
    open Equiv
