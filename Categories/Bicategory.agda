{-# OPTIONS --universe-polymorphism #-}
module Categories.Bicategory where

open import Level
-- open import Data.Product using (curry; _,_)
-- open import Function using () renaming (_∘_ to _·_)

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Categories
open import Categories.Object.Terminal
open import Categories.Terminal
open import Categories.Functor using (Functor) renaming (_∘_ to _∘F_; _≡_ to _≡F_; id to idF)
open import Categories.Functor.Constant using (Constant)
open import Categories.Bifunctor using (Bifunctor; reduce-×)
open import Categories.Product using (assocʳ; πˡ; πʳ)
open import Categories.NaturalIsomorphism
open import Categories.Bicategory.Helpers using (module BicategoryHelperFunctors)

record Bicategory (o ℓ t e : Level) : Set (suc (o ⊔ ℓ ⊔ t ⊔ e)) where
  open Terminal (One {ℓ} {t} {e})
  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Category ℓ t e
    id : {A : Obj} → Functor ⊤ (A ⇒ A)
    —∘— : {A B C : Obj} → Bifunctor (B ⇒ C) (A ⇒ B) (A ⇒ C)

  _∘_ : {A B C : Obj} {L R : Category ℓ t e} → Functor L (B ⇒ C) → Functor R (A ⇒ B) → Bifunctor L R (A ⇒ C)
  _∘_ {A} {B} {C} F G = reduce-× {D₁ = B ⇒ C} {D₂ = A ⇒ B} —∘— F G

  field
    λᵤ : {A B : Obj} → NaturalIsomorphism (id ∘ idF {C = A ⇒ B}) (πʳ {C = ⊤} {A ⇒ B})
    ρᵤ : {A B : Obj} → NaturalIsomorphism (idF {C = A ⇒ B} ∘ id) (πˡ {C = A ⇒ B} {⊤})
    α : {A B C D : Obj} → NaturalIsomorphism (idF ∘ —∘—) (((—∘— ∘ idF) ∘F assocʳ (C ⇒ D) (B ⇒ C) (A ⇒ B)))

  private module BHF = BicategoryHelperFunctors(Obj)(_⇒_)(—∘—)(id)
  private module EQ = BHF.Coherence(λᵤ)(ρᵤ)(α)

  private module _⇒_ (A B : Obj) = Category (A ⇒ B)
  open _⇒_ public using () renaming (Obj to _⇒₁_)

  field
    .triangle : {A B C : Obj} (f : A ⇒₁ B) (g : B ⇒₁ C) → EQ.Triangle f g
    .pentagon : {A B C D E : Obj} (f : A ⇒₁ B) (g : B ⇒₁ C) (h : C ⇒₁ D) (i : D ⇒₁ E) 
        → EQ.Pentagon f g h i

  -- do note that most of the "convenience" definitions in the Helpers module should really 
  -- be here (but usable in both places).  Clean that up later.
