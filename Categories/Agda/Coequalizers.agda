module Categories.Agda.Coequalizers where

open import Data.Star
open import Data.Star.Properties
open import Function using (_∘′_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.HeterogeneousEquality
open import Categories.Support.PropositionalEquality
open import Categories.Support.Quotients

open import Categories.Category
open import Categories.Agda
open import Categories.Coequalizer

coeq : ∀ {ℓ} {U V} (a b : Sets ℓ [ U , V ]) → Coequalizer (Sets ℓ) a b
coeq {ℓ} {U} {V} a b = record
  { vertex = vertex
  ; arr = ⌊_⌉
  ; commute = ≣-ext λ x → qdiv (return (to x ≣-refl ≣-refl))
  ; factor = λ f eq → qelim′ f (≈-elim′ f (≣-app eq))
  ; factored = λ f eq → ≣-ext λ x → qelim-compute′ (≈-elim′ f (≣-app eq))
  ; universal = λ f eq f′ f′∘arr≣f → ≣-ext (qequate′ λ x → ≣-trans
                  (qelim-compute′ (≈-elim′ f (≣-app eq)))
                  (≣-app (≣-sym f′∘arr≣f) x))
  }
  module coeq where

  open Category (Sets ℓ)

  data Gen (x y : V) : Set ℓ where
    to : ∀ z → (a z ≣ x) → (b z ≣ y) → Gen x y
    fro : ∀ z → (a z ≣ y) → (b z ≣ x) → Gen x y

  Gen-sym : ∀ {x y} → Gen x y → Gen y x
  Gen-sym (to  z eq eq′) = fro z eq eq′
  Gen-sym (fro z eq eq′) = to  z eq eq′

  Gen-elim : ∀ {P : V → Set ℓ} (f : ∀ x → P x) → (∀ x → f (a x) ≅ f (b x))
             → ∀ {i j} → Gen i j → f i ≅ f j
  Gen-elim f eqs (to z ≣-refl ≣-refl) = eqs z
  Gen-elim f eqs (fro z ≣-refl ≣-refl) = sym (eqs z)

  Gen-elim′ : ∀ {A : Set ℓ} (f : V → A) → (∀ x → f (a x) ≣ f (b x))
             → ∀ {i j} → Gen i j → f i ≣ f j
  Gen-elim′ f eqs (to z ≣-refl ≣-refl) = eqs z
  Gen-elim′ f eqs (fro z ≣-refl ≣-refl) = ≣-sym (eqs z)

  _≈_ = Star Gen

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record
    { refl = ε
    ; sym = reverse Gen-sym
    ; trans = _◅◅_
    }

  ≈-elim′ : ∀ {A : Set ℓ} (f : V → A) → (∀ x → f (a x) ≣ f (b x))
            → ∀ {i j} → i ≈ j → f i ≣ f j
  ≈-elim′ f eqs = gfold f _≣_ (≣-trans ∘′ Gen-elim′ f eqs) ≣-refl

  vertex : Set ℓ
  vertex = Quotient V _≈_ ≈-equiv
