module Categories.Agda.Product where

open import Categories.Category
open import Categories.Agda
import Categories.Object.Product as P
import Categories.Object.BinaryProducts as BP

open import Data.Product
open import Relation.Binary.PropositionalEquality

private
  module Dummy ℓ where
    open P (Sets ℓ)
    open BP (Sets ℓ)

    binaryProducts : BinaryProducts
    binaryProducts = record
      { product = λ {A} {B} → record
        { A×B = A × B
        ; π₁ = proj₁
        ; π₂ = proj₂
        ; ⟨_,_⟩ = <_,_>
        ; commute₁ = refl
        ; commute₂ = refl
        ; universal = universal′
        }
      }
      where
      universal′ : ∀ {A B C : Set ℓ} {f : C → A} {g : C → B} {i : C → A × B} → (λ x → proj₁ (i x)) ≡ f → (λ x → proj₂ (i x)) ≡ g → (λ x → f x , g x) ≡ i
      universal′ refl refl = refl

open Dummy public
