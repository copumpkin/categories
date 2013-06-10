{-# OPTIONS --universe-polymorphism #-}
module Categories.FunctorCategory where

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor hiding (equiv; id; _≡_; promote)
open import Categories.NaturalTransformation

Functorsᵉ : ∀ {o a} {o′ a′} → Category o a → Category o′ a′ → EasyCategory _ _ _
Functorsᵉ C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≡_ = _≡_
  ; compose = _∘₁_
  ; id = id
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc₁ {X = f} {g} {h}
  ; identityˡ = λ {_} {_} {f} → identity₁ˡ {X = f}
  ; identityʳ = λ {_} {_} {f} → identity₁ʳ {X = f}
  ; promote = promote
  ; REFL = ≣-refl
  }

Functors : ∀ {o a} {o′ a′} → Category o a → Category o′ a′ → Category _ _
Functors C D = EASY Functorsᵉ C D

Functors-rel : ∀ {o a} {o′ a′} (C : Category o a) (D : Category o′ a′) → EasyRel (Functors C D) _
Functors-rel C D = record { _≡_ = _≡_; promote = promote; REFL = ≣-refl }
