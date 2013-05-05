open import Categories.Category

module Categories.End {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {V : Category o′ ℓ′ e′} where

module C = Category C
module V = Category V
open import Categories.Bifunctor
open import Categories.DinaturalTransformation
open DinaturalTransformation using (α)
open import Categories.Functor.Constant
open import Level

record End-data (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    E : V.Obj
    π : DinaturalTransformation {C = C} (Constant E) F
    

record End (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    Data : End-data F

  open End-data Data

  IsUni : (Q : End-data F) → (u : End-data.E Q V.⇒ E) → Set _
  IsUni Q u = ∀ c → α π c V.∘ u V.≡ α (End-data.π Q) c

  field
    universal : (Q : End-data F) → End-data.E Q V.⇒ E

    .π[c]∘universal≡δ[c] : {Q : End-data F} → IsUni Q (universal Q)

    .universal-unique : {Q : End-data F} → ∀ u → IsUni Q u → u V.≡ universal Q

  open End-data Data public
