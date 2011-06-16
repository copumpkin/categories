{-# OPTIONS --universe-polymorphism #-}
module Categories.FunctorCategory where

open import Categories.Category
open import Categories.Functor hiding (equiv; id; _∘_; _≡_)
open import Categories.NaturalTransformation

Functors : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Category _ _ _
Functors C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≡_ = _≡_
  ; _∘_ = _∘₁_
  ; id = id
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc₁ {X = f} {g} {h}
  ; identityˡ = λ {_} {_} {f} → identity₁ˡ {X = f}
  ; identityʳ = λ {_} {_} {f} → identity₁ʳ {X = f}
  ; equiv = λ {F} {G} → equiv {F = F} {G = G}
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} → ∘₁-resp-≡ {f = f} {h} {g} {i}
  }