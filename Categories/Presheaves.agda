{-# OPTIONS --universe-polymorphism #-}
module Categories.Presheaves where

open import Categories.Category
open import Categories.Agda
open import Categories.FunctorCategory

{-
Preshaves : ∀ {o ℓ e : Level} → Category o ℓ e → Category {!!} {!!} {!!}
Preshaves {o} {ℓ} {e} C = Functors (Category.op C) (Setoids {!!} {!!})
-}