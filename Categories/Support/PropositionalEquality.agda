{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public using () renaming (_≡_ to _≣_; refl to ≣-refl; trans to ≣-trans; sym to ≣-sym; cong to ≣-cong; cong₂ to ≣-cong₂; subst to ≣-subst; subst₂ to ≣-subst₂; isEquivalence to ≣-isEquivalence; setoid to ≣-setoid)

module ≣-reasoning = Relation.Binary.PropositionalEquality.≡-Reasoning renaming (_≡⟨_⟩_ to _≣⟨_⟩_)

≣-subst₂-breakdown-lr : ∀ {a} {A : Set a} {b} {B : Set b} {ℓ} (f : A → B → Set ℓ) {a₁ a₂ : A} (a₁≣a₂ : a₁ ≣ a₂) {b₁ b₂ : B} (b₁≣b₂ : b₁ ≣ b₂) (x : f a₁ b₁) → ≣-subst₂ f a₁≣a₂ b₁≣b₂ x ≣ ≣-subst (f a₂) b₁≣b₂ (≣-subst (λ y → f y b₁) a₁≣a₂ x)
≣-subst₂-breakdown-lr f ≣-refl ≣-refl x = ≣-refl

≣-subst₂-breakdown-rl : ∀ {a} {A : Set a} {b} {B : Set b} {ℓ} (f : A → B → Set ℓ) {a₁ a₂ : A} (a₁≣a₂ : a₁ ≣ a₂) {b₁ b₂ : B} (b₁≣b₂ : b₁ ≣ b₂) (x : f a₁ b₁) → ≣-subst₂ f a₁≣a₂ b₁≣b₂ x ≣ ≣-subst (λ y → f y b₂) a₁≣a₂ (≣-subst (f a₁) b₁≣b₂ x)
≣-subst₂-breakdown-rl f ≣-refl ≣-refl x = ≣-refl

≣-subst-trans : ∀ {a} {A : Set a} {ℓ} (f : A → Set ℓ) {a₁ a₂ a₃ : A} (a₁≣a₂ : a₁ ≣ a₂) (a₂≣a₃ : a₂ ≣ a₃) (x : f a₁) → ≣-subst f (≣-trans a₁≣a₂ a₂≣a₃) x ≣ ≣-subst f a₂≣a₃ (≣-subst f a₁≣a₂ x)
≣-subst-trans f ≣-refl ≣-refl x = ≣-refl
