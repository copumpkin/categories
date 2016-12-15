{-# OPTIONS --universe-polymorphism #-}
module Categories.Bicategory.Helpers where

-- quite a bit of the code below is taken from Categories.2-Category
open import Data.Nat using (_+_)
open import Function using (flip)
open import Data.Product using (_,_; curry)

open import Categories.Category
open import Categories.Categories using (Categories)
import Categories.Functor
open import Categories.Terminal using (OneC; One; unit)
open import Categories.Object.Terminal using (module Terminal)
open import Categories.Bifunctor hiding (identityˡ; identityʳ; assoc) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)
open import Categories.Product using (Product; assocʳ; πˡ; πʳ)

module BicategoryHelperFunctors {o ℓ t e} (Obj : Set o) (_⇒_ : (A B : Obj) → Category ℓ t e)
    (—⊗— : {A B C : Obj} → Bifunctor (B ⇒ C) (A ⇒ B) (A ⇒ C)) 
    (id : {A : Obj} → Functor {ℓ} {t} {e} OneC (A ⇒ A)) where

  open Terminal (One {ℓ} {t} {e})

  _∘_ : {A B C : Obj} {L R : Category ℓ t e} → Functor L (B ⇒ C) → Functor R (A ⇒ B) → Bifunctor L R (A ⇒ C)
  _∘_ {A} {B} {C} F G = reduce-× {D₁ = B ⇒ C} {D₂ = A ⇒ B} —⊗— F G

  -- convenience!
  module _⇒_ (A B : Obj) = Category (A ⇒ B)
  open _⇒_ public using () renaming (Obj to _⇒₁_)

  private module imp⇒ {X Y : Obj} = Category (X ⇒ Y)
  open imp⇒ public using () renaming (_⇒_ to _⇒₂_; id to id₂; _∘_ to _•_; _≡_ to _≡₂_)

  id₁ : ∀ {A} → A ⇒₁ A
  id₁ {A} = Functor.F₀ (id {A}) unit

  id₁₂ : ∀ {A} → id₁ {A} ⇒₂ id₁ {A}
  id₁₂ {A} = id₂ {A = id₁ {A}}

  infixr 9 _∘₁_
  _∘₁_ : ∀ {A B C} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘₁_ = curry (Functor.F₀ —⊗—)

  -- horizontal composition
  infixr 9 _∘₂_
  _∘₂_ : ∀ {A B C} {g g′ : B ⇒₁ C} {f f′ : A ⇒₁ B} (β : g ⇒₂ g′) (α : f ⇒₂ f′) → (g ∘₁ f) ⇒₂ (g′ ∘₁ f′)
  _∘₂_ = curry (Functor.F₁ —⊗—)

  -- left whiskering
  infixl 9 _◃_
  _◃_ : ∀ {A B C} {g g′ : B ⇒₁ C} → g ⇒₂ g′ → (f : A ⇒₁ B) → (g ∘₁ f) ⇒₂ (g′ ∘₁ f)
  β ◃ f = β ∘₂ id₂

  -- right whiskering
  infixr 9 _▹_
  _▹_ : ∀ {A B C} (g : B ⇒₁ C) → {f f′ : A ⇒₁ B} → f ⇒₂ f′ → (g ∘₁ f) ⇒₂ (g ∘₁ f′)
  g ▹ α = id₂ ∘₂ α

  module Coherence
      (identityˡ : {A B : Obj} → NaturalIsomorphism  (id ∘ idF {C = A ⇒ B}) (πʳ {C = ⊤} {A ⇒ B}))
      (identityʳ : {A B : Obj} → NaturalIsomorphism (idF {C = A ⇒ B} ∘ id) (πˡ {C = A ⇒ B}))
      (assoc : {A B C D : Obj} → NaturalIsomorphism  (idF ∘ —⊗—) ((—⊗— ∘ idF) ∘F assocʳ (C ⇒ D) (B ⇒ C) (A ⇒ B)) ) where

    open Categories.NaturalTransformation.NaturalTransformation

     -- left/right are inverted between in certain situations!
    -- private so as to not clash with the ones in Bicategory itself
    private
      ρᵤ : {A B : Obj} (f : A ⇒₁ B) → (id₁ ∘₁ f) ⇒₂ f
      ρᵤ f = η (NaturalIsomorphism.F⇒G identityˡ) (unit , f)

      λᵤ : {A B : Obj} (f : A ⇒₁ B) → (f ∘₁ id₁) ⇒₂ f
      λᵤ f = η (NaturalIsomorphism.F⇒G identityʳ) (f , unit)

      α : {A B C D : Obj} (f : A ⇒₁ B) (g : B ⇒₁ C) (h : C ⇒₁ D) →
          (h ∘₁ (g ∘₁ f)) ⇒₂ ((h ∘₁ g) ∘₁ f)
      α f g h = η (NaturalIsomorphism.F⇒G assoc) (h , g , f)

    -- Triangle identity.  Look how closely it matches with the one on
    -- http://ncatlab.org/nlab/show/bicategory
    Triangle : {A B C : Obj} (f : A ⇒₁ B) (g : B ⇒₁ C) → Set e
    Triangle f g = (g ▹ ρᵤ f) ≡₂ ((λᵤ g ◃ f) • (α f id₁ g))

    -- Pentagon identity.  Ditto.
    Pentagon : {A B C D E : Obj} (f : A ⇒₁ B) (g : B ⇒₁ C) (h : C ⇒₁ D) (i : D ⇒₁ E) → Set e
    Pentagon f g h i = ((α g h i ◃ f) • (α f (h ∘₁ g) i)) • (i ▹ α f g h) ≡₂ (α f g (i ∘₁ h) • α (g ∘₁ f) h i)
