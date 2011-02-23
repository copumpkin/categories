{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public
open import Category.Morphisms

infix  4 _≡_

record _≡_ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′) where
  private module C = Category.Category C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
  private module D = Category.Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_) 
  open Functor F hiding (module C; module D)
  open Functor G hiding (module C; module D) renaming (F₀ to G₀; F₁ to G₁)
  open C
  open D

  field
    preserve₀ : ∀ x → F₀ x ≣ G₀ x
    preserve₁ : ∀ {A B} (f : C.Hom A B) → F₁ f ≡D (≣-subst₂ D.Hom (≣-sym (preserve₀ A)) (≣-sym (preserve₀ B)) (G₁ f))

{-
.equiv : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (_≡_ {C = C} {D = D})
equiv {C = C} {D} = record 
  { refl = refl′
  ; sym = sym′
  ; trans = {!!}
  }
  where
  module C = Category.Category C
  module D = Category.Category D

  refl′ : {F : Functor C D} → F ≡ F
  refl′ {F} = record 
    { preserve₀ = λ x → ≣-refl
    ; preserve₁ = λ f → F-resp-≡ (IsEquivalence.refl C.equiv)
    }
    where open Functor F hiding (module C)

  sym′ : {F G : Functor C D} → F ≡ G → G ≡ F
  sym′ {F} {G} pf = record 
    { preserve₀ = λ x → ≣-sym (preserve₀ x)
    ; preserve₁ = λ f → {!!}
    }
    where
    open _≡_ pf
    open IsEquivalence D.equiv
    module F = Functor F hiding (module C; module D)
    module G = Functor G hiding (module C; module D) renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    open F
    open G
-}