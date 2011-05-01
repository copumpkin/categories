{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Cartesian where

open import Support hiding (⊤; ⟨_,_⟩) renaming (_×_ to _×′_)
open import Category
open import Category.Monoidal
open import Category.Object.Product
open import Category.Object.BinaryProducts
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
      { isoˡ = identityʳ-isoˡ
      ; isoʳ = commute₁
      }
    }
  ; assoc = record 
    { F⇒G = record 
      { η = λ X → assocˡ
      ; commute = {!!}
      }
    ; F⇐G = record 
      { η = λ X → assocʳ
      ; commute = {!!}
      }
    ; iso = λ X → record 
      { isoˡ = Iso.isoʳ C (_≅_.iso C ×-assoc)
      ; isoʳ = Iso.isoˡ C (_≅_.iso C ×-assoc)
      }
    }
  ; triangle = {!!} -- λ {X} → triangle {X}
  ; pentagon = λ {X} → pentagon {X}
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

  .identityˡ-isoˡ : ∀ {X} → ⟨ ! , id ⟩ ∘ π₂ ≡ id
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
  
  .identityʳ-isoˡ : ∀ {X} → ⟨ id , ! ⟩ ∘ π₁ ≡ id
  identityʳ-isoˡ {X} = 
    begin
      ⟨ id {X} , ! ⟩ ∘ π₁
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ π₁ , ! ∘ π₁ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (IsEquivalence.sym equiv identityˡ) (!-unique (! ∘ π₁))) ⟩
      ⟨ π₁ , ! ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) (!-unique (! ∘ π₂)) ⟩
      ⟨ π₁ , ! ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) (∘-resp-≡ˡ (⊤-id !)) ⟩
      ⟨ π₁ , id ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) identityˡ ⟩
      ⟨ π₁ , π₂ ⟩
    ≈⟨ η ⟩
      id
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

{-
  -- The implicit x is actually used implicitly by the rest of the expression, so don't take it out,
  -- or Agda will complain about something referring to something to which it has no access.
  -- The connection between the mentioned x and the rest of the type is given by the caller way up
  -- there, so if that were not using these the triangle and pentagon laws would be yellow.
  .triangle : ∀ {x} → first π₁ ≡ second π₂ ∘ assocˡ
  triangle = 
    begin
      first π₁
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (IsEquivalence.refl equiv) commute₂) ⟩
      ⟨ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym second∘⟨⟩ ⟩
      second π₂ ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv    

  .pentagon : ∀ {x} → assocˡ ∘ assocˡ ≡ second assocˡ ∘ (assocˡ ∘ first assocˡ)
  pentagon =
    begin
      assocˡ ∘ assocˡ
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ assocˡ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ assocˡ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc ⟨⟩∘ ⟩
      ⟨ π₁ ∘ (π₁ ∘ assocˡ) , ⟨ (π₂ ∘ π₁) ∘ assocˡ , π₂ ∘ assocˡ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ʳ commute₁) (⟨⟩-cong₂ assoc commute₂) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ (π₁ ∘ assocˡ) , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) (⟨⟩-cong₂ (∘-resp-≡ʳ commute₁) (IsEquivalence.refl equiv)) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      second assocˡ ∘ (assocˡ ∘ first assocˡ)
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv
-}
  .pentagon : ∀ {x} → assocˡ ∘ assocˡ ≡ second assocˡ ∘ (assocˡ ∘ first assocˡ)
  pentagon {x} = ?