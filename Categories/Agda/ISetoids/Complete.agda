module Categories.Agda.ISetoids.Complete where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder; module Preorder; Rel; _=[_]⇒_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Categories.Support.IProduct
-- import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Support.Equivalence using (module I→R-Wrapper; setoid-i→r; Fam-setoid; ∀[_]-setoid_) 
                                           renaming (Setoid to ISetoid; module Setoid to ISetoid)
open import Categories.Support.SetoidFunctions using (module _⟶_)
open import Categories.Support.PropositionalEquality
import Categories.Support.ZigZag as ZigZag

open import Categories.Category
open import Categories.Functor
import Categories.NaturalTransformation as NT
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone

ISetoidsComplete : ∀ {o ℓ e c ℓ′} → Cocomplete o ℓ e (Category.op (ISetoids (c ⊔ ℓ′ ⊔ (o ⊔ ℓ ⊔ e)) (c ⊔ (o ⊔ ℓ ⊔ e))))
ISetoidsComplete {o} {ℓ} {e} {c} {cℓ} = record { colimit = colimit }
  where
  c′ = c ⊔ cℓ ⊔ (o ⊔ ℓ ⊔ e)
  ℓ′ = c ⊔ (o ⊔ ℓ ⊔ e)
  C = Category.op (ISetoids c′ ℓ′)
  colimit : ∀ {J : Category o ℓ e} (F : Functor J C) → Colimit F
  colimit {J} F = record { initial = record 
    { ⊥ = record 
          { N = Fam-setoid (Σ′ (∀ j → Carrier (F₀ j)) (λ f → ∀ {a b} (h : a J.⇒ b) → (F₀ a ≈ F₁ h ⟨$⟩ f b) (f a)))
                           (∀[ J.Obj ]-setoid F₀) proj₁′ 
          ; ψ = λ X → record 
              { _⟨$⟩_ = λ f → proj₁′ f X
              ; cong  = λ eq → eq X 
              }
          ; commute = λ {X} {Y} h {f} {g} f≈g → trans (F₀ X) (f≈g X) (sym (F₀ X) (proj₂′ g h))
          }
    ; ! = λ {A} → record 
          { f = record 
              { _⟨$⟩_ = λ X → (λ j → Cocone.ψ A j ⟨$⟩ X) , (λ {a} {b} h → sym (F₀ a) (Cocone.commute A h (refl (Cocone.N A))))
              ; cong  = λ i≈j a → cong (Cocone.ψ A a) i≈j 
              }
           ; commute = λ {X} x≈y → cong (Cocone.ψ A X) x≈y 
           }
    ; !-unique = λ {A} f x≈y a → sym (F₀ a) (CoconeMorphism.commute f (sym (Cocone.N A) x≈y)) 
    } }
    where
    module J = Category J
    open Functor F
    open ISetoid
    open _⟶_
