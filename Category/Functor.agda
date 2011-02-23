{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public
open import Category.Morphisms

infix  4 _≡_

data [_]_∼_ {o ℓ e} (C : Category o ℓ e) {A B} (f : Category.Hom C A B) : ∀ {X Y} → Category.Hom C X Y → Set (o ⊔ ℓ ⊔ e) where
  refl : {g : Category.Hom C A B} → Category._≡_ C f g → [ C ] f ∼ g

-- Universe too high here and above. FIXME!
_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (F G : Functor C D) → Set (o ⊔ ℓ ⊔ e′ ⊔ o′ ⊔ ℓ′ ⊔ e′)
_≡_ {C = C} {D} F G = ∀ {A B} → (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f

.equiv : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (_≡_ {C = C} {D = D})
equiv {C = C} {D} = record 
  { refl = λ {F} → refl′ {F}
  ; sym = λ {F} {G} → sym′ {F} {G}
  ; trans = {!!}
  }
  where
  module C = Category.Category C
  module D = Category.Category D

  refl′ : {F : Functor C D} {A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ F f
  refl′ {F} f = refl {C = D} (Functor.F-resp-≡ F (IsEquivalence.refl C.equiv))

  sym′ : {F G : Functor C D} → 
        ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f) →
        ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ G f ∼ Functor.F₁ F f)
  sym′ {F} {G} F∼G {A} {B} f = {!!}
