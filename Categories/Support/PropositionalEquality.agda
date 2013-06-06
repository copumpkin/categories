{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.PropositionalEquality where

open import Function using (flip; id)
open import Relation.Binary.PropositionalEquality public using () renaming (_≡_ to _≣_; refl to ≣-refl; trans to ≣-trans; sym to ≣-sym; cong to ≣-cong; cong₂ to ≣-cong₂; subst to ≣-subst; subst₂ to ≣-subst₂; isEquivalence to ≣-isEquivalence; setoid to ≣-setoid)

module ≣-reasoning = Relation.Binary.PropositionalEquality.≡-Reasoning renaming (_≡⟨_⟩_ to _≣⟨_⟩_)

≣-app : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : (x : A) → B x} → f ≣ g → (x : A) → f x ≣ g x
≣-app {f = f} {g} = flip (λ x → ≣-cong (flip id x))

≣-appʰ : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : ∀ {x} → B x} → (λ {x} → f) ≣ g → ∀ {x} → f {x} ≣ g {x}
≣-appʰ {f = f} {g} = λ pf {x} → ≣-cong (λ h → h {x}) pf

≣-subst₂-breakdown-lr : ∀ {a} {A : Set a} {b} {B : Set b} {ℓ} (f : A → B → Set ℓ) {a₁ a₂ : A} (a₁≣a₂ : a₁ ≣ a₂) {b₁ b₂ : B} (b₁≣b₂ : b₁ ≣ b₂) (x : f a₁ b₁) → ≣-subst₂ f a₁≣a₂ b₁≣b₂ x ≣ ≣-subst (f a₂) b₁≣b₂ (≣-subst (λ y → f y b₁) a₁≣a₂ x)
≣-subst₂-breakdown-lr f ≣-refl ≣-refl x = ≣-refl

≣-subst₂-breakdown-rl : ∀ {a} {A : Set a} {b} {B : Set b} {ℓ} (f : A → B → Set ℓ) {a₁ a₂ : A} (a₁≣a₂ : a₁ ≣ a₂) {b₁ b₂ : B} (b₁≣b₂ : b₁ ≣ b₂) (x : f a₁ b₁) → ≣-subst₂ f a₁≣a₂ b₁≣b₂ x ≣ ≣-subst (λ y → f y b₂) a₁≣a₂ (≣-subst (f a₁) b₁≣b₂ x)
≣-subst₂-breakdown-rl f ≣-refl ≣-refl x = ≣-refl

≣-subst-trans : ∀ {a} {A : Set a} {ℓ} (f : A → Set ℓ) {a₁ a₂ a₃ : A} (a₁≣a₂ : a₁ ≣ a₂) (a₂≣a₃ : a₂ ≣ a₃) (x : f a₁) → ≣-subst f (≣-trans a₁≣a₂ a₂≣a₃) x ≣ ≣-subst f a₂≣a₃ (≣-subst f a₁≣a₂ x)
≣-subst-trans f ≣-refl ≣-refl x = ≣-refl

≣-cong₂₊ : ∀ {a b c r} {A : Set a} {B : Set b} {C : A → B → Set c} {R : Set r} (f : (x : A) → (u : B) → .(z : C x u) → R) {x y : A} {u v : B} .(z : C x u) → (x≣y : x ≣ y) (u≣v : u ≣ v) → f x u z ≣ f y v (≣-subst₂ C x≣y u≣v z)
≣-cong₂₊ f z ≣-refl ≣-refl = ≣-refl
