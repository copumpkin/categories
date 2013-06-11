-- http://ncatlab.org/nlab/show/coequalizer
open import Categories.Category

module Categories.Coequalizer {o a} (C : Category o a) where

open import Level

open import Categories.Operations

aℓ = a
open Category C

record Coequalizer {U V} (a b : U ⇒ V) : Set (o ⊔ aℓ) where
  field
    {vertex} : _
    arr : V ⇒ vertex
    .commute : arr ∘ a ≡ arr ∘ b
    factor : ∀ {Y} (f : V ⇒ Y) → .(f ∘ a ≡ f ∘ b) → vertex ⇒ Y
    .factored : ∀ {Y} (f : V ⇒ Y) .(eq : f ∘ a ≡ f ∘ b) → factor f eq ∘ arr ≡ f
    .universal : ∀ {Y} (f : V ⇒ Y) .(eq : f ∘ a ≡ f ∘ b) (f′ : vertex ⇒ Y)
               → f′ ∘ arr ≡ f → factor f eq ≡ f′
