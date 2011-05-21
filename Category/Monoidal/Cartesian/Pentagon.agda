{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Cartesian.Pentagon where

open import Support hiding (⊤; ⟨_,_⟩) renaming (_×_ to _×′_)
open import Category
open import Category.Monoidal
open import Category.Object.BinaryProducts using (BinaryProducts)
open import Category.Object.BinaryProducts.Abstract
open import Category.Object.Products
open import Category.Object.Terminal
open import Category.Bifunctor using (Bifunctor)
open import Category.Morphisms
open import Category.Square

module Law {o ℓ e : Level} (C : Category o ℓ e) (P : BinaryProducts C) where
  open Category.Category C
  open AbstractBinaryProducts C P

  .π₁∘assocˡ : ∀ {X Y Z} → π₁ ∘ assocˡ {X} {Y} {Z} ≡ π₁ ∘ π₁
  π₁∘assocˡ =
    begin
      π₁ ∘ assocˡ
    ≈⟨ ∘-resp-≡ʳ (prop assocˡ-convert) ⟩
      π₁ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ commute₁ ⟩
      π₁ ∘ π₁
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .π₂∘assocˡ : ∀ {X Y Z} → π₂ ∘ assocˡ {X} {Y} {Z} ≡ ⟨ π₂ ∘ π₁ , π₂ ⟩
  π₂∘assocˡ =
    begin
      π₂ ∘ assocˡ
    ≈⟨ ∘-resp-≡ʳ (prop assocˡ-convert) ⟩
      π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ commute₂ ⟩
      ⟨ π₂ ∘ π₁ , π₂ ⟩
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .π₁₁-assocˡ : ∀ {X Y Z W} → (π₁ ∘ π₁) ∘ assocˡ {_} {Z} {W} ≡ (π₁ ∘ π₁) ∘ first (assocˡ {X} {Y} {Z})
  π₁₁-assocˡ = 
    begin
      (π₁ ∘ π₁) ∘ assocˡ
    ≈⟨ glue (sym π₁∘assocˡ) π₁∘assocˡ ⟩
      π₁ ∘ (assocˡ ∘ π₁)
    ≈⟨ ∘-resp-≡ʳ (sym π₁∘⁂) ⟩
      π₁ ∘ (π₁ ∘ first assocˡ)
    ≈⟨ sym assoc ⟩
      (π₁ ∘ π₁) ∘ first assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv
    open GlueSquares C

  abstract
    mess : ∀ {A B C D} → (((A × B) × C) × D) ⇒ (B × C)
    mess = ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩

    .mess-convert : ∀ {A B C D} → mess {A} {B} {C} {D} ≣ ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩
    mess-convert = ≣-refl

    .π₁∘mess : ∀ {A B C D} → π₁ ∘ mess {A} {B} {C} {D} ≡ (π₂ ∘ π₁) ∘ π₁
    π₁∘mess = commute₁

    .π₂∘mess : ∀ {A B C D} → π₂ ∘ mess {A} {B} {C} {D} ≡ π₂ ∘ π₁
    π₂∘mess = commute₂

  abstract
    bigmess : ∀ {A B C D} → (((A × B) × C) × D) ⇒ ((B × C) × D)
    bigmess = ⟨ mess , π₂ ⟩

    .bigmess-convert : ∀ {A B C D} → bigmess {A} {B} {C} {D} ≣ ⟨ mess , π₂ ⟩
    bigmess-convert = ≣-refl

    .π₁∘bigmess : ∀ {A B C D} → π₁ ∘ bigmess ≡ mess {A} {B} {C} {D}
    π₁∘bigmess = commute₁

    .π₂∘bigmess : ∀ {A B C D} → π₂ ∘ bigmess {A} {B} {C} {D} ≡ π₂
    π₂∘bigmess = commute₂

  .⟨π₂∘π₁,π₂⟩∘assocˡ : ∀ {X Y Z W} → ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ ≡ assocˡ ∘ bigmess {X} {Y} {Z} {W}
  ⟨π₂∘π₁,π₂⟩∘assocˡ =
    begin
      ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ assocˡ , π₂ ∘ assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc refl ⟩
      ⟨ π₂ ∘ (π₁ ∘ assocˡ) , π₂ ∘ assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ʳ π₁∘assocˡ) π₂∘assocˡ ⟩
      ⟨ π₂ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (sym assoc) (⟨⟩-cong₂ (sym π₂∘mess) refl) ⟩
      ⟨ (π₂ ∘ π₁) ∘ π₁ , ⟨ π₂ ∘ mess , π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (sym π₁∘mess) (⟨⟩-cong₂ (∘-resp-≡ʳ (sym π₁∘bigmess)) refl) ⟩
      ⟨ π₁ ∘ mess , ⟨ π₂ ∘ (π₁ ∘ bigmess) , π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ʳ (sym π₁∘bigmess)) (⟨⟩-cong₂ (sym assoc) (sym π₂∘bigmess)) ⟩
      ⟨ π₁ ∘ (π₁ ∘ bigmess) , ⟨ (π₂ ∘ π₁) ∘ bigmess , π₂ ∘ bigmess ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (sym assoc) (sym ⟨⟩∘) ⟩
      ⟨ (π₁ ∘ π₁) ∘ bigmess , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ bigmess ⟩
    ≈⟨ sym ⟨⟩∘ ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ bigmess
    ≈⟨ ∘-resp-≡ˡ (sym (prop assocˡ-convert)) ⟩
      assocˡ ∘ bigmess
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv

  .⟨π₂∘π₁,π₂⟩∘first-assocˡ : ∀ {X Y Z W} → ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ first assocˡ ≡ bigmess {X} {Y} {Z} {W}
  ⟨π₂∘π₁,π₂⟩∘first-assocˡ =
    begin
      ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ first assocˡ
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₂ ∘ π₁) ∘ first assocˡ , π₂ ∘ first assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ (glue◃◽ π₂∘assocˡ π₁∘⁂) π₂∘⁂ ⟩
      ⟨ ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ π₁ , id ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ ⟨⟩∘ identityˡ ⟩
      ⟨ ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩ , π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (sym (prop mess-convert)) refl ⟩
      ⟨ mess , π₂ ⟩
    ≈⟨ sym (prop bigmess-convert) ⟩
      bigmess
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv
    open GlueSquares C

  .pentagon : ∀ {X Y Z W} → assocˡ {X} {Y} ∘ assocˡ ≡ second (assocˡ {Y} {Z} {W}) ∘ (assocˡ ∘ first (assocˡ {X}))
  pentagon = 
    begin
      assocˡ ∘ assocˡ
    ≈⟨ ∘-resp-≡ˡ (prop assocˡ-convert) ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ assocˡ
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ refl ⟨π₂∘π₁,π₂⟩∘assocˡ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , assocˡ ∘ bigmess ⟩
    ≈⟨ ⟨⟩-cong₂ π₁₁-assocˡ (∘-resp-≡ʳ (sym ⟨π₂∘π₁,π₂⟩∘first-assocˡ)) ⟩
      ⟨ (π₁ ∘ π₁) ∘ first assocˡ , assocˡ ∘ (⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ first assocˡ) ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ˡ (sym identityˡ)) (sym assoc) ⟩    
      ⟨ (id ∘ (π₁ ∘ π₁)) ∘ first assocˡ , (assocˡ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩) ∘ first assocˡ ⟩
    ≈⟨ sym ⟨⟩∘ ⟩
      ⟨ id ∘ (π₁ ∘ π₁) , assocˡ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ first assocˡ
    ≈⟨ ∘-resp-≡ˡ (sym ⁂∘⟨⟩) ⟩
      (second assocˡ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩) ∘ first assocˡ
    ≈⟨ ∘-resp-≡ˡ (∘-resp-≡ʳ (sym (prop assocˡ-convert))) ⟩
      (second assocˡ ∘ assocˡ) ∘ first assocˡ
    ≈⟨ assoc ⟩ 
      second assocˡ ∘ (assocˡ ∘ first assocˡ)
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv