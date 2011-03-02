{-# OPTIONS --universe-polymorphism #-}
module Category.Agda where

open import Support
open import Category

Agda : ∀ {o} → Category _ _ _
Agda {o} = record
  { Obj = Set o
  ; Hom = λ d c → d → c
  ; _≡_ = λ f g → ∀ x → f x ≣ g x

  ; _∘_ = λ f g x → f (g x)
  ; id = λ x → x

  ; assoc = λ f → ≣-refl
  ; identityˡ = λ x → ≣-refl
  ; identityʳ = λ x → ≣-refl
  ; equiv = record { refl = λ x → ≣-refl; sym = s; trans = t }
  ; ∘-resp-≡ = ∘-resp-≡′
  }
  where
  s : {A B : Set o} → {i j : A → B} → ((x : A) → i x ≣ j x) → (x : A) → j x ≣ i x
  s f x rewrite f x = ≣-refl

  t : {A B : Set o} {i j k : A → B} → ((x : A) → i x ≣ j x) → ((x : A) → j x ≣ k x) → (x : A) → i x ≣ k x
  t f g x rewrite f x | g x = ≣-refl

  ∘-resp-≡′ : {A B C : Set o} {f h : B → C} {g i : A → B} →
             (∀ x → f x ≣ h x) →
             (∀ x → g x ≣ i x) → 
             (∀ x → f (g x) ≣ h (i x))
  ∘-resp-≡′ {g = g} f≡h g≡i x rewrite f≡h (g x) | g≡i x = ≣-refl