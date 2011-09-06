{-# OPTIONS --universe-polymorphism #-}

module Categories.Support.SetoidFunctions where

open import Level
open import Function using (_on_)
open import Relation.Binary as B using (_=[_]⇒_)
open import Relation.Binary.PropositionalEquality using () renaming (cong to ≡-cong; cong₂ to ≡-cong₂)
open import Data.Product using (<_,_>; _×_; _,_)

open import Categories.Support.Equivalence

infixr 0 _⟶_

record _⟶_ {cf ℓf ct ℓt} (From : Setoid cf ℓf) (To : Setoid ct ℓt) :
         Set (cf ⊔ ℓf ⊔ ct ⊔ ℓt) where
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : (x : Setoid.Carrier From) → Setoid.Carrier To
    .cong  : Setoid._≈_ From =[ _⟨$⟩_ ]⇒ Setoid._≈_ To

open _⟶_ public

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = Function.id; cong = Function.id }

infixr 9 _∙_

_∙_ : ∀ {ca ℓa} {A : Setoid ca ℓa}
        {cb ℓb} {B : Setoid cb ℓb}
        {cc ℓc} {C : Setoid cc ℓc} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∙ g = record
  { _⟨$⟩_ = Function._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong = Function._∘_ (cong f) (cong g)
  }

const : ∀ {ca ℓa} {A : Setoid ca ℓa}
          {cb ℓb} {B : Setoid cb ℓb} →
        Setoid.Carrier B → A ⟶ B
const {B = B} b = record
  { _⟨$⟩_ = Function.const b
  ; cong = Function.const (Setoid.refl B)
  }

→-to-⟶ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (set→setoid A ⟶ set→setoid B)
→-to-⟶ f = record { _⟨$⟩_ = f; cong = ≡-cong f }

------------------------------------------------------------------------
-- Function setoids

setoid : ∀ {cf ℓf ct ℓt}
         (From : Setoid cf ℓf) →
         Setoid ct ℓt →
         Setoid _ _
setoid From To = record
  { Carrier       = From ⟶ To
  ; _≈_           = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  ; isEquivalence = record
    { refl  = λ {f} → cong f
    ; sym   = λ f∼g x∼y → To.sym (f∼g (From.sym x∼y))
    ; trans = λ f∼g g∼h x∼y → To.trans (f∼g From.refl) (g∼h x∼y)
    }
  }
  where
  open module From = Setoid From using () renaming (_≈_ to _≈₁_)
  open module To = Setoid To using () renaming (_≈_ to _≈₂_)

infixr 0 _⇨_

_⇨_ : ∀ {cf ℓf ct ℓt} → Setoid cf ℓf → Setoid ct ℓt → Setoid _ _
From ⇨ To = setoid From To

⟪_,_⟫ : ∀ {cf ℓf ct₁ ℓt₁ ct₂ ℓt₂} {From : Setoid cf ℓf} {To₁ : Setoid ct₁ ℓt₁} {To₂ : Setoid ct₂ ℓt₂} (f₁ : From ⟶ To₁) (f₂ : From ⟶ To₂) → (From ⟶ (To₁ ×-setoid To₂))
⟪ f₁ , f₂ ⟫ = record { _⟨$⟩_ = < (_⟨$⟩_ f₁) , (_⟨$⟩_ f₂) >
                     ; cong = < cong f₁ , cong f₂ > }

⟪_,_⟫′ : ∀ {cf ℓf ct₁ ct₂} {From : Setoid cf ℓf} {To₁ : Set ct₁} {To₂ : Set ct₂} (f₁ : From ⟶ set→setoid To₁) (f₂ : From ⟶ set→setoid To₂) → (From ⟶ set→setoid (To₁ × To₂))
⟪ f₁ , f₂ ⟫′ = record { _⟨$⟩_ = < (_⟨$⟩_ f₁) , (_⟨$⟩_ f₂) >
                      ; cong = λ x≈y → ≡-cong₂ _,_ (cong f₁ x≈y) (cong f₂ x≈y) }