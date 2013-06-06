{-# OPTIONS --universe-polymorphism #-}
module Categories.Comma.Functors where

open import Categories.Category
open import Categories.Functor renaming (_∘_ to _∘F_)
open import Categories.FunctorCategory renaming (Functors to [_⇒_])
open import Categories.NaturalTransformation using (module NaturalTransformation)
open import Data.Product using (∃; _,_; proj₁; proj₂; zip; map)
open import Level
open import Relation.Binary using (Rel)
open import Categories.Support.EqReasoning
open import Categories.Square

open import Categories.Comma
open import Categories.Product renaming (Product to _×_)

πComma :
  ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
    → {A : Category o₁ ℓ₁ e₁}
    → {B : Category o₂ ℓ₂ e₂}
    → {C : Category o₃ ℓ₃ e₃}
    → (S : Functor B C) (T : Functor A C)
    → Functor (S ↓ T) (B × A)
πComma {A = A} {B} {C} S T =
  record
    { F₀ = F₀′
    ; F₁ = F₁′
    ; identity = B×A.Equiv.refl
    ; homomorphism = B×A.Equiv.refl
    ; F-resp-≡ = λ pf → pf
    }
  where
    module S↓T = Category (S ↓ T)
    module B×A = Category (B × A)
    open Comma S T using (_,_[_]) renaming (_,_,_ to ⟨_,_,_⟩)

    F₀′ : S↓T.Obj → B×A.Obj
    F₀′ ⟨ α , β , f ⟩ = α , β

    F₁′ : ∀ {X Y} → (S ↓ T) [ X , Y ] → (B × A) [ F₀′ X , F₀′ Y ]
    F₁′ (g , h [ commutes ]) = g , h

InducedFunctor : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
                   {A : Category o₁ ℓ₁ e₁}
                   {B : Category o₂ ℓ₂ e₂}
                   {C : Category o₃ ℓ₃ e₃}
                   {s₁ s₂ d₁ d₂}
                   (m : (Category.op [ A ⇒ C ] × [ B ⇒ C ]) [ (s₁ , s₂) , (d₁ , d₂) ])
                 → Functor (s₁ ↓ s₂) (d₁ ↓ d₂)
InducedFunctor {A = A} {B} {C} {s₁} {s₂} {d₁} {d₂} m = record
  { F₀ = F₀′
  ; F₁ = F₁′
  ; identity = λ {X} → d₁↓d₂.Equiv.refl {_} {_} {d₁↓d₂.id {F₀′ X}}
  ; homomorphism = λ {_ _ _ f g} → d₁↓d₂.Equiv.refl {_} {_} {F₁′ ((s₁ ↓ s₂) [ g ∘ f ])}
  ; F-resp-≡ = λ pf → pf
  }
  where
  module s₁↓s₂ = Category (s₁ ↓ s₂)
  module d₁↓d₂ = Category (d₁ ↓ d₂)
  module s₁ = Functor s₁
  module s₂ = Functor s₂
  module d₁ = Functor d₁
  module d₂ = Functor d₂
  module m₁ = NaturalTransformation (proj₁ m)
  module m₂ = NaturalTransformation (proj₂ m)

  open Category C
  open Comma renaming (_,_,_ to ⟨_,_,_⟩)

  F₀′ : s₁↓s₂.Obj → d₁↓d₂.Obj
  F₀′ ⟨ α , β , f ⟩ = ⟨ α , β , m₂.η β ∘ f ∘ m₁.η α ⟩

  F₁′ : ∀ {X Y} → (s₁ ↓ s₂) [ X , Y ] → (d₁ ↓ d₂) [ F₀′ X , F₀′ Y ]
  F₁′ {⟨ α₁ , β₁ , f₁ ⟩} {⟨ α₂ , β₂ , f₂ ⟩} (g , h [ commutes ]) = g , h [ ( 
      begin
        d₂.F₁ h ∘ m₂.η β₁ ∘ f₁ ∘ m₁.η α₁
      ↑⟨ pushˡ (m₂.commute h) ⟩
        (m₂.η β₂ ∘ s₂.F₁ h) ∘ f₁ ∘ m₁.η α₁
      ↓⟨ pullˡ (pullʳ commutes) ⟩
        (m₂.η β₂ ∘ f₂ ∘ s₁.F₁ g) ∘ m₁.η α₁
      ↑⟨ extendˡ (extendˡ (m₁.commute g)) ⟩
        (m₂.η β₂ ∘ f₂ ∘ m₁.η α₂) ∘ d₁.F₁ g
      ∎ ) ]
    where
    open HomReasoning
    open GlueSquares C
