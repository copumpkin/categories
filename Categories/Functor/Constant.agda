{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Constant where

open import Categories.Category
open import Categories.Functor

Constant : ∀ {o′ a′} {D : Category o′ a′} (x : Category.Obj D) → ∀ {o a} {C : Category o a} → Functor C D
Constant {D = D} x = record
                     { F₀ = λ _ → x
                     ; F₁ = λ _ → D.id
                     ; identity = D.Equiv.refl
                     ; homomorphism = D.Equiv.sym D.identityˡ
                     }
                     where
                     module D = Category D
