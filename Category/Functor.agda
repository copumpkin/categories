{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public
open import Category.Morphisms

infix  4 _≡_

data [_]_∼_ {o ℓ e} (C : Category o ℓ e) {A B} (f : Category.Hom C A B) : ∀ {X Y} → Category.Hom C X Y → Set (ℓ ⊔ e) where
  refl : {g : Category.Hom C A B} → Category._≡_ C f g → [ C ] f ∼ g

-- Universe too high here and above. FIXME!
_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (F G : Functor C D) → Set (e′ ⊔ ℓ′ ⊔ ℓ ⊔ o)
_≡_ {C = C} {D} F G = ∀ {A B} → (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f

.equiv : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (_≡_ {C = C} {D = D})
equiv {C = C} {D} = record 
  { refl = λ {F} → refl′ {F}
  ; sym = λ {F} {G} → sym′ {F} {G}
  ; trans = λ {F} {G} {H} → trans′ {F} {G} {H}
  }
  where
  module C = Category.Category C
  module D = Category.Category D

  refl′ : {F : Functor C D} {A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ F f
  refl′ {F} f = refl {C = D} (Functor.F-resp-≡ F (IsEquivalence.refl C.equiv))

  sym′ : {F G : Functor C D} → 
        ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f) →
        ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ G f ∼ Functor.F₁ F f)
  sym′ {F} {G} F∼G {A} {B} f = helper (Functor.F₀ F A) (Functor.F₀ F B) (Functor.F₀ G A) (Functor.F₀ G B) (Functor.F₁ F f) (Functor.F₁ G f) (F∼G f)
    where -- with blocks aren't smart enough to do this
    helper : (a b c d : Category.Obj D)
           → (f : Category.Hom D a b)
           → (g : Category.Hom D c d)
           → [ D ] f ∼ g
           → [ D ] g ∼ f
    helper .c .d c d F G (refl pf) = refl {C = D} (IsEquivalence.sym (Category.equiv D) pf)

  trans′ : {F G H : Functor C D} →
         ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f) →
         ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ G f ∼ Functor.F₁ H f) →
         ({A B : Category.Obj C} (f : Category.Hom C A B) → [ D ] Functor.F₁ F f ∼ Functor.F₁ H f)
  trans′ {F} {G} {H} F∼G G∼H {A} {B} f = 
         helper (Functor.F₀ F A) (Functor.F₀ F B) (Functor.F₀ G A) (Functor.F₀ G B) (Functor.F₀ H A) (Functor.F₀ H B) 
                (Functor.F₁ F f) (Functor.F₁ G f) (Functor.F₁ H f) (F∼G f) (G∼H f)
    where
    helper : (a b c d x y : Category.Obj D)
           → (f : Category.Hom D a b)
           → (g : Category.Hom D c d)
           → (h : Category.Hom D x y)
           → [ D ] f ∼ g
           → [ D ] g ∼ h
           → [ D ] f ∼ h
    helper .x .y .x .y x y f g h (refl pf₀) (refl pf₁) = refl {C = D} (IsEquivalence.trans (Category.equiv D) pf₀ pf₁)

