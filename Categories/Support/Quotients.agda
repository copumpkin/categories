module Categories.Support.Quotients where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H

postulate
  Quotient : ∀ {c ℓ} (Carrier : Set c) (_≈_ : Rel Carrier ℓ) (isEquivalence : IsEquivalence _≈_) → Set (c ⊔ ℓ)

  ⌊_⌉ : ∀ {c ℓ} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} → Carrier → Quotient Carrier _≈_ isEquivalence

  qelim : ∀ {c ℓ p} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {P : Quotient Carrier _≈_ isEquivalence → Set p} (m : (x : Carrier) → P ⌊ x ⌉) .(cong : ∀ {x y} → x ≈ y → m x ≅ m y) → (q : Quotient Carrier _≈_ isEquivalence) → P q

  qelim-compute : ∀ {c ℓ p} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {P : Quotient Carrier _≈_ isEquivalence → Set p} {m : (x : Carrier) → P ⌊ x ⌉} .(cong : ∀ {x y} → x ≈ y → m x ≅ m y) → {x : Carrier} → qelim {isEquivalence = isEquivalence}{P} m cong ⌊ x ⌉ ≡ m x

  qdiv : ∀ {c ℓ} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} → {x y : Carrier} → .(x ≈ y) → _≡_ {A = Quotient Carrier _≈_ isEquivalence} ⌊ x ⌉ ⌊ y ⌉

  -- i could make isEquivalence truly irrelevant but there would be so much yellow it should be worth the red
  Quotient-irrelevant : ∀ {c ℓ} (Carrier : Set c) (_≈_ : Rel Carrier ℓ) (isEquivalence₁ isEquivalence₂ : IsEquivalence _≈_) → Quotient Carrier _≈_ isEquivalence₁ ≡ Quotient Carrier _≈_ isEquivalence₂

qelim′ : ∀ {c ℓ p} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {P : Set p} (m : (x : Carrier) → P) .(cong : ∀ {x y} → x ≈ y → m x ≡ m y) → (q : Quotient Carrier _≈_ isEquivalence) → P
qelim′ {P = P} m congg = qelim {P = λ _ → P} m (λ eq → ≡-to-≅ (congg eq))

qelim-compute′ : ∀ {c ℓ p} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {P : Set p} {m : (x : Carrier) → P} .(cong : ∀ {x y} → x ≈ y → m x ≡ m y) → {x : Carrier} → qelim′ {isEquivalence = isEquivalence}{P} m cong ⌊ x ⌉ ≡ m x
qelim-compute′ {P = P} {m} congg = qelim-compute {P = λ _ → P} {m} (λ eq → ≡-to-≅ (congg eq))

private
  heterrelevance′ : ∀ {a} {A : Set a} {x y x′ y′ : A}
                  → (eq : x ≡ y) (eq′ : x′ ≡ y′)
                  → x ≡ x′ → y ≡ y′ → eq ≅ eq′
  heterrelevance′ refl refl refl refl = refl

  heterrelevance : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} {C : Set ℓ} {D : Set ℓ}
                 → {x : A} {y : B} {x′ : C} {y′ : D}
                 → (eq : x ≅ y) (eq′ : x′ ≅ y′)
                 → x ≅ x′ → y ≅ y′ → eq ≅ eq′
  heterrelevance refl refl refl refl = refl

qequate′-coherent : ∀ {c ℓ a} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {A : Set a} (f g : Quotient Carrier _≈_ isEquivalence → A) (eq : (x : Carrier) → f ⌊ x ⌉ ≡ g ⌊ x ⌉) → ∀ {x y} → x ≈ y → eq x ≅ eq y
qequate′-coherent f g eq = λ x≈y → heterrelevance′ _ _ (P.cong f (qdiv x≈y)) (P.cong g (qdiv x≈y))

qequate′ : ∀ {c ℓ a} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {A : Set a} {f g : Quotient Carrier _≈_ isEquivalence → A} (eq : (x : Carrier) → f ⌊ x ⌉ ≡ g ⌊ x ⌉) → ∀ q → f q ≡ g q
qequate′ {f = f} {g} eq = qelim eq (qequate′-coherent f g eq)

qequate-coherent : ∀ {c ℓ a} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {A B : Quotient Carrier _≈_ isEquivalence → Set a} (f : ∀ x → A x) (g : ∀ x → B x) (eq : (x : Carrier) → f ⌊ x ⌉ ≅ g ⌊ x ⌉) → ∀ {x y} → x ≈ y → eq x ≅ eq y
qequate-coherent f g eq = λ x≈y → heterrelevance _ _ (H.cong f (≡-to-≅ (qdiv x≈y))) (H.cong g (≡-to-≅ (qdiv x≈y)))

qequate : ∀ {c ℓ a} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {isEquivalence : IsEquivalence _≈_} {A B : Quotient Carrier _≈_ isEquivalence → Set a} {f : ∀ x → A x} {g : ∀ x → B x} (eq : (x : Carrier) → f ⌊ x ⌉ ≅ g ⌊ x ⌉) → ∀ q → f q ≅ g q
qequate {f = f} {g} eq = qelim eq (qequate-coherent f g eq)

