{-# OPTIONS --universe-polymorphism #-}
open import Relation.Binary

module Data.Star.Equality {o ℓ e} {Obj : Set o} (S : Obj → Obj → Setoid ℓ e) where

open import Data.Star
import Data.Star.Properties as Props
open import Level
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)

private
  open module S i j = Setoid (S i j)
    using () renaming (Carrier to T)
  _≊_ : ∀ {i j} → Rel (T i j) e
  _≊_ {i}{j} = S._≈_ i j

infix 4 _≈_

data _≈_ : {i₁ i₂ : Obj} → Rel (Star T i₁ i₂) (o ⊔ ℓ ⊔ e) where
  ε-cong : ∀ {i} → ε {x = i} ≈ ε {x = i}
  _◅-cong_ : {i j k : Obj}{x₁ x₂ : T i j} {xs₁ xs₂ : Star T j k}
    → x₁ ≊ x₂
    → xs₁ ≈ xs₂
    → (x₁ ◅ xs₁) ≈ (x₂ ◅ xs₂)

_◅◅-cong_ : {i j k : Obj}{xs₁ xs₂ : Star T i j} {ys₁ ys₂ : Star T j k}
    → xs₁ ≈ xs₂
    → ys₁ ≈ ys₂
    → (xs₁ ◅◅ ys₁) ≈ (xs₂ ◅◅ ys₂)
ε-cong         ◅◅-cong p   = p
(p ◅-cong ps₁) ◅◅-cong ps₂ = p ◅-cong (ps₁ ◅◅-cong ps₂)


private
  refl : ∀ {i j} → Reflexive (_≈_ {i}{j})
  refl {x = ε} = ε-cong
  refl {x = x ◅ xs} = S.refl _ _ ◅-cong refl

  sym : ∀ {i j} → Symmetric (_≈_ {i}{j})
  sym ε-cong = ε-cong
  sym (px ◅-cong pxs) = S.sym _ _ px ◅-cong sym pxs
  
  trans : ∀ {i j} → Transitive (_≈_ {i}{j})
  trans ε-cong ε-cong = ε-cong
  trans (px₁ ◅-cong pxs₁) (px₂ ◅-cong pxs₂)
    = S.trans _ _ px₁ px₂ ◅-cong trans pxs₁ pxs₂

isEquivalence : ∀ {i j} → IsEquivalence (_≈_ {i}{j})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

private
  reflexive : ∀ {i j} {x y : Star T i j} → x ≡ y → x ≈ y
  reflexive ≡-refl = refl

StarSetoid : ∀ i j → Setoid (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
StarSetoid i j = record
  { Carrier       = Star T i j
  ; _≈_           = _≈_
  ; isEquivalence = isEquivalence
  }

◅◅-assoc : {A B C D : Obj} (f : Star T A B) (g : Star T B C) (h : Star T C D)
  → ((f ◅◅ g) ◅◅ h) ≈ (f ◅◅ (g ◅◅ h))
◅◅-assoc f g h = reflexive (Props.◅◅-assoc f g h)

▻▻-assoc : {A B C D : Obj} (f : Star T A B) (g : Star T B C) (h : Star T C D)
  → ((h ▻▻ g) ▻▻ f) ≈ (h ▻▻ (g ▻▻ f))
▻▻-assoc f g h = sym (◅◅-assoc f g h)
