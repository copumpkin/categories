{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public

open import Category.NaturalIsomorphism

infix  4 _≡_

_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Rel (Functor C D) _
_≡_ = NaturalIsomorphism

.assoc : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {o′′′ ℓ′′′ e′′′} 
           {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o′′ ℓ′′ e′′} {D : Category o′′′ ℓ′′′ e′′′}
       → {F : Functor A B} → {G : Functor B C} → {H : Functor C D} → (H ∘ G) ∘ F ≡ H ∘ (G ∘ F)
assoc {F = F} {G} {H} = 
    begin
      (H ∘ G) ∘ F
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      H ∘ (G ∘ F)
    ∎
  where
  open IsEquivalence equiv
  open SetoidReasoning setoid

  module F = Functor F
  module G = Functor G
  module H = Functor H