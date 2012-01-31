{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Equivalence.Strong where

open import Level
open import Relation.Binary using (IsEquivalence)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Functor hiding (equiv)
open import Categories.Functor.Properties
import Categories.Morphisms as Morphisms

record StrongEquivalence {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    .full : Full F
    .faithful : Faithful F
    eso : EssentiallySurjective F

record StronglyEquivalent {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    C⇒D : Functor C D
    strong-equivalence : StrongEquivalence C⇒D
  open StrongEquivalence strong-equivalence public

refl : ∀ {o ℓ e} {C : Category o ℓ e} → StronglyEquivalent C C
refl {C = C} = record
  { C⇒D = id
  ; strong-equivalence = record
    { full = λ {X Y} → my-full X Y
    ; faithful = λ _ _ eq → eq
    ; eso = λ d → d , (record { f = C.id; g = C.id; iso = record { isoˡ = C.identityˡ; isoʳ = C.identityˡ } })
    }
  }
  where
  module C = Category C
  open C hiding (id)
  .my-full : ∀ X Y → ¬ Σ (X ⇒ Y) (λ f → ¬ ∃ (λ g → C [ g ≡ f ]))
  my-full X Y (f , elim) = elim (f , Equiv.refl)

sym : ∀ {o ℓ e o′ ℓ′ e′} → {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → StronglyEquivalent C D → StronglyEquivalent D C
sym {C = C} {D = D} Op = record
  { C⇒D = record
    { F₀ = λ d → proj₁ (Op.eso d)
    ; F₁ = λ f → {!rev (proj₂ (Op.eso _)) ∘ f ∘ ?!}
    ; identity = {!!}
    ; homomorphism = {!!}
    ; F-resp-≡ = {!!}
    }
  ; strong-equivalence = record
    { full = {!!}
    ; faithful = {!!}
    ; eso = {!!}
    }
  }
  where
  module Op = StronglyEquivalent Op
  open Op using () renaming (C⇒D to F)
  open Functor F
  open Morphisms._≅_ C renaming (f to fwd; g to rev)

trans : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂} {C₃ : Category o₃ ℓ₃ e₃} → StronglyEquivalent C₁ C₂ → StronglyEquivalent C₂ C₃ → StronglyEquivalent C₁ C₃
trans {C₁ = C₁} {C₂} {C₃} C₁⇒C₂ C₂⇒C₃ = record
  { C⇒D = G ∘ F
  ; strong-equivalence = record
    { full = λ {X Y} → my-full X Y
    ; faithful = λ f g → C₁⇒C₂.faithful _ _ ∙ C₂⇒C₃.faithful _ _
    ; eso = my-eso }
  }
  where
  module C₁⇒C₂ = StronglyEquivalent C₁⇒C₂
  module C₂⇒C₃ = StronglyEquivalent C₂⇒C₃
  open C₁⇒C₂ using () renaming (C⇒D to F)
  open C₂⇒C₃ using () renaming (C⇒D to G)
  module F = Functor F
  open F using (F₀; F₁)
  module G = Functor G
  open G using () renaming (F₀ to G₀; F₁ to G₁)
  module E = Category.Equiv C₃
  open Morphisms C₃
  .my-full : ∀ X Y → ¬ ∃ (λ f → ¬ ∃ (λ (g : C₁ [ X , Y ]) → C₃ [ G₁ (F₁ g) ≡ f ]))
  my-full X Y (f , elim) = C₂⇒C₃.full (f , lemma)
    where
    lemma : ¬ ∃ (λ h → C₃ [ G₁ h ≡ f ])
    lemma (h , G₁h≡f) = C₁⇒C₂.full (h , lemma₂)
      where
      lemma₂ : ¬ ∃ (λ g → C₂ [ F₁ g ≡ h ])
      lemma₂ (g , F₁g≡h) = elim (g , E.trans (G.F-resp-≡ F₁g≡h) G₁h≡f)
  my-eso : ∀ c₃ → ∃ (λ c₁ → G₀ (F₀ c₁) ≅ c₃)
  my-eso c₃ with C₂⇒C₃.eso c₃
  my-eso c₃ | c₂ , ff₃ with C₁⇒C₂.eso c₂
  my-eso c₃ | c₂ , ff₃ | c₁ , ff₂ = c₁ , (ff₃ ⓘ resp-≅ ff₂)
    where open FunctorsAlways G

equiv : ∀ {o ℓ e} → IsEquivalence (StronglyEquivalent {o} {ℓ} {e})
equiv = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }