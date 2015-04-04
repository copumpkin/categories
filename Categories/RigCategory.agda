module Categories.RigCategory where

open import Level
open import Data.Fin renaming (zero to 0F; suc to sucF)
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Functor
open import Categories.Monoidal
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.Monoidal.Helpers
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)

module BimonoidalHelperFunctors {o ℓ e} {C : Category o ℓ e} 
  {M⊎ M× : Monoidal C} {B⊎ : Braided M⊎} (S⊎ : Symmetric B⊎)
   (B× : Braided M×) where

  private
    module C = Category C
    module M⊎ = Monoidal M⊎
    module M× = Monoidal M×
    module B⊎ = Braided B⊎
    module B× = Braided B×

  module h⊎ = MonoidalHelperFunctors C M⊎.⊗ M⊎.id
  module h× = MonoidalHelperFunctors C M⊎.⊗ M×.id
  module b⊎ = BraidedHelperFunctors C M⊎.⊗ M⊎.id
  module b× = BraidedHelperFunctors C M×.⊗ M×.id

  import Categories.Power.NaturalTransformation
  private module PowNat = Categories.Power.NaturalTransformation C
  open PowNat hiding (module C)


  x⊗[y⊕z] : Powerendo 3
  x⊗[y⊕z] = h×.x h×.⊗ (h⊎.x⊗y)

  [x⊕y]⊗z : Powerendo 3
  [x⊕y]⊗z = (h⊎.x⊗y) h×.⊗ h×.x

  [x⊗y]⊕[x⊗z] : Powerendo 3
  [x⊗y]⊕[x⊗z] = (select 0 h×.⊗₂ select 1) h⊎.⊗₂ (select 0 h×.⊗₂ select 2) 

  [x⊗z]⊕[y⊗z] : Powerendo 3
  [x⊗z]⊕[y⊗z] = (select 0 h×.⊗₂ select 2) h⊎.⊗₂ (select 1 h×.⊗₂ select 2)

  x⊗0 : Powerendo 1
  x⊗0 = h⊎.x h×.⊗ h⊎.id↑

  0⊗x : Powerendo 1
  0⊗x = h⊎.id↑ h×.⊗ h⊎.x

  0↑ : Powerendo 1
  0↑ = widenˡ 1 h⊎.id↑

record RigCategory {o ℓ e} {C : Category o ℓ e} 
  {M⊎ M× : Monoidal C} {B⊎ : Braided M⊎} {S⊎ : Symmetric B⊎}
   {B× : Braided M×} : Set (o ⊔ ℓ ⊔ e) where


  open BimonoidalHelperFunctors S⊎ B×

  field
    distribₗ : NaturalIsomorphism x⊗[y⊕z] [x⊗y]⊕[x⊗z]
    distribᵣ : NaturalIsomorphism [x⊕y]⊗z [x⊗z]⊕[y⊗z]
    annₗ : NaturalIsomorphism x⊗0 0↑
    annᵣ : NaturalIsomorphism 0⊗x 0↑
