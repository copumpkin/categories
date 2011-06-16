{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Constant where

open import Categories.Category
open import Categories.Functor

Constant : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (x : Category.Obj D) → ∀ {o ℓ e} {C : Category o ℓ e} → Functor C D
Constant {D = D} x = record
                     { F₀ = λ _ → x
                     ; F₁ = λ _ → D.id
                     ; identity = D.Equiv.refl
                     ; homomorphism = D.Equiv.sym D.identityˡ
                     ; F-resp-≡ = λ _ → D.Equiv.refl
                     }
                     where
                     module D = Category D
