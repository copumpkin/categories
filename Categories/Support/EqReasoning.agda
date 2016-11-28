{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.EqReasoning where

open import Categories.Support.Equivalence using (Setoid; module Setoid)
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≣_; trans to ≣-trans; sym to ≣-sym; refl to ≣-refl)

module SetoidReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open Setoid S

  infix  4 _IsRelatedTo_
  infix  1 begin_
  infixr 2 _≈⟨_⟩_ _↓⟨_⟩_ _↑⟨_⟩_ _↓≣⟨_⟩_ _↑≣⟨_⟩_ _↕_
  infix  3 _∎
  
  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : Carrier) : Set s₂ where
    relTo : (x∼y : x ≈ y) → x IsRelatedTo y

  .begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
  begin relTo x∼y = x∼y

  ._↓⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
    -- where open IsEquivalence isEquivalence

  ._↑⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑⟨ y∼x ⟩ relTo y∼z = relTo (trans (sym y∼x) y∼z)
    -- where open IsEquivalence isEquivalence

  -- the syntax of the ancients, for compatibility
  ._≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _≈⟨_⟩_ = _↓⟨_⟩_

  ._↓≣⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↑≣⟨_⟩_ : ∀ x {y z} → y ≣ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑≣⟨ ≣-refl ⟩ y∼z = y∼z

  ._↕_ : ∀ x {z} → x IsRelatedTo z → x IsRelatedTo z
  _ ↕ x∼z = x∼z

  ._∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl
    -- where open IsEquivalence isEquivalence

module ≣-reasoning {ℓ} (S : Set ℓ) where
  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _≈⟨_⟩_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infixr 2 _↕_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : S) : Set ℓ where
    relTo : (x∼y : x ≣ y) → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ≣ y
  begin relTo x∼y = x∼y

  -- the syntax of the ancients, for compatibility
  _≈⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x∼y ⟩ relTo y∼z = relTo (≣-trans x∼y y∼z)

  _↓⟨_⟩_ : ∀ x {y z} → x ≣ y → y IsRelatedTo z → x IsRelatedTo z
  _ ↓⟨ x∼y ⟩ relTo y∼z = relTo (≣-trans x∼y y∼z)

  _↑⟨_⟩_ : ∀ x {y z} → y ≣ x → y IsRelatedTo z → x IsRelatedTo z
  _ ↑⟨ y∼x ⟩ relTo y∼z = relTo (≣-trans (≣-sym y∼x) y∼z)

  _↕_ : ∀ x {z} → x IsRelatedTo z → x IsRelatedTo z
  _ ↕ x∼z = x∼z

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo ≣-refl

