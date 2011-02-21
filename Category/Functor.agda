{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Support
open import Category
open import Category.Functor.Core public
open import Category.NaturalIsomorphism
open import Category.Morphisms

infix  4 _≡_

-- Equality on functors is natural isomorphism? This feels odd. 
-- The proofs below are also too easy with this equality. Something must be wrong!
_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Rel (Functor C D) _
_≡_ = NaturalIsomorphism

identityˡ : ∀ {o ℓ e} {o′ ℓ′ e′}
              {A : Category o ℓ e} {B : Category o′ ℓ′ e′}
          → {F : Functor A B} → id ∘ F ≡ F
identityˡ {A = A} {B} {F} = record 
  { F⇒G = record 
    { η = λ _ → F₁ A.id
    ; commute = F⇐⇒G-commute
    }
  ; F⇐G = record 
    { η = λ _ → F₁ A.id
    ; commute = F⇐⇒G-commute
    }
  ; iso = iso
  }
  where
  module A = Category.Category A renaming (_∘_ to _∘A_; _≡_ to _≡A_)
  module B = Category.Category B renaming (_∘_ to _∘B_; _≡_ to _≡B_)
  module F = Functor F
  open F
  open A
  open B

  .F⇐⇒G-commute : ∀ {X Y} (f : A.Hom X Y) → F₁ A.id ∘B F₁ f ≡B F₁ f ∘B F₁ A.id
  F⇐⇒G-commute f = begin
                      F₁ A.id ∘B F₁ f
                    ≈⟨ sym F.homomorphism ⟩
                      F₁ (A.id ∘A f)
                    ≈⟨ F-resp-≡ A.identityˡ ⟩
                      F₁ f
                    ≈⟨ sym (F-resp-≡ A.identityʳ)  ⟩
                      F₁ (f ∘A A.id)
                    ≈⟨ F.homomorphism ⟩
                      F₁ f ∘B F₁ A.id
                    ∎
    where
    open IsEquivalence B.equiv
    open SetoidReasoning B.hom-setoid

  .iso : ∀ X → Iso B (F₁ (A.id {X})) (F₁ A.id)
  iso X = record 
    { isoˡ = iso′
    ; isoʳ = iso′
    }
    where
    iso′ : F₁ A.id ∘B F₁ A.id ≡B B.id
    iso′ = begin
             F₁ A.id ∘B F₁ A.id
           ≈⟨ sym homomorphism ⟩
             F₁ (A.id ∘A A.id)
           ≈⟨ F-resp-≡ A.identityˡ ⟩
             F₁ A.id
           ≈⟨ identity ⟩
             B.id
           ∎
      where 
      open IsEquivalence B.equiv
      open SetoidReasoning B.hom-setoid


.assoc : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {o′′′ ℓ′′′ e′′′} 
           {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o′′ ℓ′′ e′′} {D : Category o′′′ ℓ′′′ e′′′}
       → {F : Functor A B} → {G : Functor B C} → {H : Functor C D} → (H ∘ G) ∘ F ≡ H ∘ (G ∘ F)
assoc {A = A} {B} {C} {D} {F} {G} {H} = record 
  { F⇒G = record 
    { η = λ _ → H₁ (G₁ (F₁ A.id))
    ; commute = F⇐⇒G-commute
    }
  ; F⇐G = record 
    { η = λ _ → H₁ (G₁ (F₁ A.id))
    ; commute = F⇐⇒G-commute
    }
  ; iso = iso
  }
  where
  module A = Category.Category A
  module B = Category.Category B
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F hiding (module C; module D)
  module G = Functor G hiding (module C; module D)
  module H = Functor H hiding (module C; module D)
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
  open D renaming (_∘_ to _∘D_; _≡_ to _≡D_)

  F⇐⇒G-commute : ∀ {X Y} (f : A.Hom X Y) → H₁ (G₁ (F₁ A.id)) ∘D H₁ (G₁ (F₁ f)) ≡D H₁ (G₁ (F₁ f)) ∘D H₁ (G₁ (F₁ A.id))
  F⇐⇒G-commute f = begin
                     H₁ (G₁ (F₁ A.id)) ∘D H₁ (G₁ (F₁ f))
                   ≈⟨ ∘-resp-≡ˡ (H-resp-≡ (G-resp-≡ F.identity)) ⟩
                     H₁ (G₁ B.id) ∘D H₁ (G₁ (F₁ f))
                   ≈⟨ ∘-resp-≡ˡ (H-resp-≡ G.identity) ⟩
                     H₁ C.id ∘D H₁ (G₁ (F₁ f))
                   ≈⟨ ∘-resp-≡ˡ H.identity ⟩
                     D.id ∘D H₁ (G₁ (F₁ f))
                   ≈⟨ D.identityˡ ⟩
                     H₁ (G₁ (F₁ f))
                   ≈⟨ sym D.identityʳ ⟩
                     H₁ (G₁ (F₁ f)) ∘D D.id
                   ≈⟨ sym (∘-resp-≡ʳ H.identity) ⟩
                     H₁ (G₁ (F₁ f)) ∘D H₁ C.id
                   ≈⟨ sym (∘-resp-≡ʳ (H-resp-≡ G.identity)) ⟩
                     H₁ (G₁ (F₁ f)) ∘D H₁ (G₁ B.id)
                   ≈⟨ sym (∘-resp-≡ʳ (H-resp-≡ (G-resp-≡ F.identity))) ⟩
                     H₁ (G₁ (F₁ f)) ∘D H₁ (G₁ (F₁ A.id))
                   ∎
    where
    open IsEquivalence D.equiv
    open SetoidReasoning D.hom-setoid

  .iso : ∀ X → Iso D (H₁ (G₁ (F₁ (A.id {X})))) (H₁ (G₁ (F₁ A.id)))
  iso X = record 
    { isoˡ = iso′
    ; isoʳ = iso′
    }
    where
    iso′ : H₁ (G₁ (F₁ A.id)) ∘D H₁ (G₁ (F₁ A.id)) ≡D D.id
    iso′ = begin
             H₁ (G₁ (F₁ A.id)) ∘D H₁ (G₁ (F₁ A.id))
           ≈⟨ ∘-resp-≡ (H-resp-≡ (G-resp-≡ F.identity)) (H-resp-≡ (G-resp-≡ F.identity)) ⟩
             H₁ (G₁ B.id) ∘D H₁ (G₁ B.id)
           ≈⟨ ∘-resp-≡ (H-resp-≡ G.identity) (H-resp-≡ G.identity) ⟩
             H₁ C.id ∘D H₁ C.id
           ≈⟨ ∘-resp-≡ H.identity H.identity ⟩
             D.id ∘D D.id
           ≈⟨ D.identityˡ ⟩
             D.id
           ∎
      where
      open SetoidReasoning D.hom-setoid
