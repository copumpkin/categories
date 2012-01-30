{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.StarEquality where

open import Categories.Support.Equivalence
open import Data.Star
import Data.Star.Properties as Props
open import Level
open import Relation.Binary
  using ( Rel
        ; Reflexive; Symmetric; Transitive
        ; IsEquivalence
        ; _=[_]⇒_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)

module StarEquality {o ℓ e} {Obj : Set o} (S : Obj → Obj → Setoid ℓ e) where
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

  _▻▻-cong_ : {i j k : Obj}{xs₁ xs₂ : Star T j k} {ys₁ ys₂ : Star T i j}
      → xs₁ ≈ xs₂
      → ys₁ ≈ ys₂
      → (xs₁ ▻▻ ys₁) ≈ (xs₂ ▻▻ ys₂)
  x ▻▻-cong y = y ◅◅-cong x

  private
    .refl : ∀ {i j} → Reflexive (_≈_ {i}{j})
    refl {x = ε} = ε-cong
    refl {x = x ◅ xs} = S.refl _ _ ◅-cong refl

    .sym : ∀ {i j} → Symmetric (_≈_ {i}{j})
    sym ε-cong = ε-cong
    sym (px ◅-cong pxs) = S.sym _ _ px ◅-cong sym pxs
  
    .trans : ∀ {i j} → Transitive (_≈_ {i}{j})
    trans ε-cong ε-cong = ε-cong
    trans (px₁ ◅-cong pxs₁) (px₂ ◅-cong pxs₂)
      = S.trans _ _ px₁ px₂ ◅-cong trans pxs₁ pxs₂

  .isEquivalence : ∀ {i j} → IsEquivalence (_≈_ {i}{j})
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  private
    .reflexive : ∀ {i j} {x y : Star T i j} → x ≡ y → x ≈ y
    reflexive ≡-refl = refl

  StarSetoid : ∀ i j → Setoid (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  StarSetoid i j = record
    { Carrier       = Star T i j
    ; _≈_           = _≈_
    ; isEquivalence = isEquivalence
    }

  .◅◅-assoc : {A B C D : Obj} (f : Star T A B) (g : Star T B C) (h : Star T C D)
    → ((f ◅◅ g) ◅◅ h) ≈ (f ◅◅ (g ◅◅ h))
  ◅◅-assoc f g h = reflexive (Props.◅◅-assoc f g h)

  .▻▻-assoc : {A B C D : Obj} (f : Star T A B) (g : Star T B C) (h : Star T C D)
    → ((h ▻▻ g) ▻▻ f) ≈ (h ▻▻ (g ▻▻ f))
  ▻▻-assoc f g h = sym (◅◅-assoc f g h)

open StarEquality public using (StarSetoid)

-- congruences involving Star lists of 2 relations
module StarCong₂ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
  {I : Set o₁} (T-setoid : I → I → Setoid ℓ₁ e₁)
  {J : Set o₂} (U-setoid : J → J → Setoid ℓ₂ e₂)
  
  where
    private
      module T i j = Setoid (T-setoid i j)
      T : Rel I ℓ₁
      T = T.Carrier
      _≊₁_ : ∀ {i j} → Rel (T i j) e₁
      _≊₁_ {i}{j} = T._≈_ i j
      module T* i j = Setoid (StarSetoid T-setoid i j)
      _≈₁_ : ∀ {i j} → Rel (Star T i j) (o₁ ⊔ ℓ₁ ⊔ e₁)
      _≈₁_ {i}{j} = T*._≈_ i j
      open StarEquality T-setoid
        using ()
        renaming (ε-cong to ε-cong₁; _◅-cong_ to _◅-cong₁_)
      
      module U i j = Setoid (U-setoid i j)
      U : Rel J ℓ₂
      U = U.Carrier
      _≊₂_ : ∀ {i j} → Rel (U i j) e₂
      _≊₂_ {i}{j} = U._≈_ i j
      module U* i j = Setoid (StarSetoid U-setoid i j)
      _≈₂_ : ∀ {i j} → Rel (Star U i j) (o₂ ⊔ ℓ₂ ⊔ e₂)
      _≈₂_ {i}{j} = U*._≈_ i j
      open StarEquality U-setoid
        using ()
        renaming (ε-cong to ε-cong₂; _◅-cong_ to _◅-cong₂_)
      
    gmap-cong : (f : I → J) (g : T =[ f ]⇒ U) (g′ : T =[ f ]⇒ U)
              → (∀ {i j} (x y : T i j) → x ≊₁ y → g x ≊₂ g′ y)
              → ∀ {i j} (xs ys : Star T i j)
              → xs ≈₁ ys
              → gmap {U = U} f g xs ≈₂ gmap f g′ ys
    gmap-cong f g g′ eq ε .ε ε-cong₁ = ε-cong₂
    gmap-cong f g g′ eq (x ◅ xs) (y ◅ ys) (x≊y ◅-cong₁ xs≈ys) 
      = (eq x y x≊y) ◅-cong₂ (gmap-cong f g g′ eq xs ys xs≈ys)
    gmap-cong f g g′ eq (x ◅ xs) ε ()
