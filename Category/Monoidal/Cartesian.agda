{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Cartesian where

open import Support hiding (⊤; ⟨_,_⟩) renaming (_×_ to _×′_)
open import Category
open import Category.Monoidal
open import Category.Object.Product
open import Category.Object.Products
open import Category.Object.Terminal
open import Category.Bifunctor using (Bifunctor)
open import Category.Morphisms

Cartesian : ∀ {o ℓ e} (C : Category o ℓ e) → Products C → Monoidal C
Cartesian C Ps = record
  { ⊗ = ⊗
  ; id = ⊤
  ; identityˡ = record 
    { F⇒G = record 
      { η = λ X → π₂
      ; commute = λ f → commute₂
      }
    ; F⇐G = record 
      { η = λ X → ⟨ ! , id ⟩
      ; commute = λ f → F⇐G-commuteˡ
      }
    ; iso = λ X → record 
      { isoˡ = identityˡ-isoˡ
      ; isoʳ = commute₂
      }
    }
  ; identityʳ = record 
    { F⇒G = record 
      { η = λ X → π₁
      ; commute = λ f → commute₁
      }
    ; F⇐G = record 
      { η = λ X → ⟨ id , ! ⟩
      ; commute = λ f → F⇐G-commuteʳ
      }
    ; iso = λ X → record 
      { isoˡ = {!!}
      ; isoʳ = commute₁
      }
    }
  ; assoc = record 
    { F⇒G = record 
      { η = λ X → _≅_.g C ×-assoc
      ; commute = {!!}
      }
    ; F⇐G = record 
      { η = λ X → _≅_.f C ×-assoc
      ; commute = {!!}
      }
    ; iso = λ X → record 
      { isoˡ = Iso.isoʳ C (_≅_.iso C ×-assoc)
      ; isoʳ = Iso.isoˡ C (_≅_.iso C ×-assoc)
      }
    }
  ; triangle = λ {X} → triangle {X}
  ; pentagon = {!!}
  }
  where
  open Category.Category C
  open Products C Ps renaming (terminal to T; binary to P)
  open BinaryProducts C P
  open Terminal C T

  ⊗ : Bifunctor C C C
  ⊗ = record 
    { F₀ = λ p → fst p × snd p
    ; F₁ = λ x → fst x ⁂ snd x
    ; identity = universal (identity-commutative π₁) (identity-commutative π₂)
    ; homomorphism = IsEquivalence.sym equiv ⁂∘⁂
    ; F-resp-≡ = λ x → ⟨⟩-cong₂ (∘-resp-≡ˡ (fst x)) (∘-resp-≡ˡ (snd x))
    }

  .F⇐G-commuteˡ : ∀ {X Y} {f : Hom X Y} → ⟨ ! , id ⟩ ∘ f ≡ second f ∘ ⟨ ! , id ⟩
  F⇐G-commuteˡ {f = f} = 
    begin
      ⟨ ! , id ⟩ ∘ f
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ ! ∘ f , id ∘ f ⟩
    ≈⟨ sym (⟨⟩-cong₂ (!-unique (! ∘ f)) (identity-commutative f)) ⟩
      ⟨ ! , f ∘ id ⟩
    ≈⟨ sym second∘⟨⟩ ⟩
      second f ∘ ⟨ ! , id ⟩
    ∎ 
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .identityˡ-isoˡ : ∀ {X} → ⟨ ! , id {X} ⟩ ∘ π₂ ≡ id
  identityˡ-isoˡ {X} = 
    begin
      ⟨ ! , id {X} ⟩ ∘ π₂
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ ! ∘ π₂ , id ∘ π₂ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (!-unique (! ∘ π₂)) (IsEquivalence.sym equiv identityˡ)) ⟩
      ⟨ ! , π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (!-unique (! ∘ π₁)) (IsEquivalence.refl equiv) ⟩
      ⟨ ! ∘ π₁ , π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ˡ (⊤-id !)) (IsEquivalence.refl equiv) ⟩
      ⟨ id ∘ π₁ , π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ identityˡ (IsEquivalence.refl equiv) ⟩
      ⟨ π₁ , π₂ ⟩
    ≈⟨ η ⟩
      id
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .F⇐G-commuteʳ : ∀ {X Y} {f : Hom X Y} → ⟨ id , ! ⟩ ∘ f ≡ first f ∘ ⟨ id , ! ⟩
  F⇐G-commuteʳ {f = f} =
    begin
      ⟨ id , ! ⟩ ∘ f
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ f , ! ∘ f ⟩
    ≈⟨ sym (⟨⟩-cong₂ (identity-commutative f) (!-unique (! ∘ f))) ⟩
      ⟨ f ∘ id , ! ⟩
    ≈⟨ sym first∘⟨⟩ ⟩
      first f ∘ ⟨ id , ! ⟩
    ∎ 
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv
  
  .triangle : {x : Obj ×′ Obj} → first π₁ ≡ second π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ 
  triangle = {!!}