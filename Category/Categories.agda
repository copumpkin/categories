{-# OPTIONS --universe-polymorphism #-}
module Category.Categories where

open import Support
open import Category
open import Category.Functor

Categories : ∀ {o ℓ e} → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Categories {o} {ℓ} {e} = record 
  { Obj = Category o ℓ e
  ; Hom = Functor
  ; _≡_ = _≡_
  ; _∘_ = _∘_
  ; id = id
  ; assoc = λ {_} {_} {_} {_} {F} {G} {H} → assoc {F = F} {G} {H}
  ; identityˡ = λ {_} {_} {F} → identityˡ {F = F}
  ; identityʳ = λ {_} {_} {F} → identityʳ {F = F}
  ; equiv = λ {X} {Y} → equiv {C = X} {D = Y}
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} → ∘-resp-≡ {F = f} {h} {g} {i}
  }