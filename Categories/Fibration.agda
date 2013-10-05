{-# OPTIONS --universe-polymorphism #-}
module Categories.Fibration where

open import Level hiding (lift)
open import Data.Product

open import Categories.Category
open import Categories.Functor hiding (_∘_; _≡_)
open import Categories.Morphism.Cartesian
import Categories.Morphisms as Morphisms

record CartesianLifting {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {E : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁}
                        (p : Functor E B) {a e} (f : B [ a , Functor.F₀ p e ]) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  private module E = Category E
  private module B = Category B
  open B using (_∘_; _≡_)

  open Functor p renaming (F₀ to p₀; F₁ to p₁)
  open Morphisms B

  field
    e′ : E.Obj

    φ : E [ e′ , e ]
    proof : ∃ \ (h : a ≅ p₀ e′) → f ∘ _≅_.g h ≡ p₁ φ
    φ-cartesian : Cartesian p φ


record Fibration {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} (E : Category o₀ ℓ₀ e₀) (B : Category o₁ ℓ₁ e₁) : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  private module E = Category E
  private module B = Category B
  open B using (_∘_; _≡_)

  field
    p : Functor E B

  open Functor p renaming (F₀ to p₀; F₁ to p₁)

  open Morphisms B

  field
    lift : ∀ {a} e → (f : B [ a  , p₀ e ]) → CartesianLifting p f
