{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.Constant where

open import Support
open import Category
open import Category.Functor

Constant : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (x : Category.Obj D) → ∀ {o ℓ e} {C : Category o ℓ e} → Functor C D
Constant {D = D} x = record
                     { F₀ = λ _ → x
                     ; F₁ = λ _ → D.id
                     ; identity = IsEquivalence.refl D.equiv
                     ; homomorphism = IsEquivalence.sym D.equiv D.identityˡ
                     ; F-resp-≡ = λ _ → IsEquivalence.refl D.equiv
                     }
                     where
                     module D = Category.Category D
