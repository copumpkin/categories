{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Cartesian where

open import Support hiding (⊤; ⟨_,_⟩) renaming (_×_ to _×′_)
open import Category
open import Category.Monoidal
open import Category.Object.BinaryProducts.Abstract
open import Category.Object.Products
open import Category.Object.Terminal
open import Category.Bifunctor using (Bifunctor)
open import Category.Morphisms
open import Category.Square
import Category.Monoidal.Cartesian.Pentagon as Pentagon

Cartesian : ∀ {o ℓ e} (C : Category o ℓ e) → Products C → Monoidal C
Cartesian C Ps = record
  { ⊗ = ⊗
  ; id = ⊤
  ; identityˡ = record
    { F⇒G = record
      { η = λ X → π₂
      ; commute = λ f → Equiv.trans (∘-resp-≡ʳ (Equiv.prop (⁂-convert id (f zero)))) commute₂
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
      ; commute = λ f → Equiv.trans (∘-resp-≡ʳ (Equiv.prop (⁂-convert (f zero) id))) commute₁
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
      ; commute = λ f → assocˡ-commute
      }
    ; F⇐G = record
      { η = λ X → assocʳ
      ; commute = λ f → assocʳ-commute
      }
    ; iso = λ X → record
      { isoˡ = Iso.isoʳ C assoc-iso
      ; isoʳ = Iso.isoˡ C assoc-iso
      }
    }
  ; triangle = λ {X} → triangle {X}
  ; pentagon = pentagon
  }
  where
  open Category.Category C
  open Products C Ps renaming (terminal to T₀; binary to P₀)
  open Terminal C T₀ using (⊤; !; !-unique; ⊤-id)

  open AbstractBinaryProducts C P₀
  open Pentagon.Law C P₀ using (pentagon)

  ⊗ : Bifunctor C C C
  ⊗ = record
    { F₀ = λ p → fst p × snd p
    ; F₁ = λ x → fst x ⁂ snd x
    ; identity = identity
    ; homomorphism = IsEquivalence.sym equiv ⁂∘⁂
    ; F-resp-≡ = λ {A B F G} x → F-resp-≡ {A} {B} {F} {G} x
    }
    where
    .identity : ∀ {A} → (id {fst A} ⁂ id {snd A}) ≡ id 
    identity =
      begin
        id ⁂ id
      ≣⟨ ⁂-convert id id ⟩
        ⟨ id ∘ π₁ , id ∘ π₂ ⟩
      ≈⟨ universal (id-comm {f = π₁}) (id-comm {f = π₂}) ⟩
        Category.id C
      ∎
      where open SetoidReasoning hom-setoid
    .F-resp-≡ : ∀ {A B F G} F≡G → _
    F-resp-≡ {F = F} {G} x = 
      begin
        fst F ⁂ snd F
      ≣⟨ ⁂-convert (fst F) (snd F) ⟩
        ⟨ fst F ∘ π₁ , snd F ∘ π₂ ⟩
      ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ˡ (fst x)) (∘-resp-≡ˡ (snd x)) ⟩
        ⟨ fst G ∘ π₁ , snd G ∘ π₂ ⟩
      ≣⟨ ≣-sym (⁂-convert (fst G) (snd G)) ⟩
        fst G ⁂ snd G
      ∎
      where open SetoidReasoning hom-setoid

  .F⇐G-commuteˡ : ∀ {X Y} {f : X ⇒ Y} → ⟨ ! , id ⟩ ∘ f ≡ second f ∘ ⟨ ! , id ⟩
  F⇐G-commuteˡ {f = f} = 
    begin
      ⟨ ! , id ⟩ ∘ f
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ ! ∘ f , id ∘ f ⟩
    ≈⟨ sym (⟨⟩-cong₂ (!-unique (! ∘ f)) (id-comm {f = f})) ⟩
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

  .F⇐G-commuteʳ : ∀ {X Y} {f : X ⇒ Y} → ⟨ id , ! ⟩ ∘ f ≡ first f ∘ ⟨ id , ! ⟩
  F⇐G-commuteʳ {f = f} =
    begin
      ⟨ id , ! ⟩ ∘ f
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ f , ! ∘ f ⟩
    ≈⟨ sym (⟨⟩-cong₂ (id-comm {f = f}) (!-unique (! ∘ f))) ⟩
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

  .assocˡ-commute : ∀ {X₀ Y₀ X₁ Y₁ X₂ Y₂} {f : X₀ ⇒ Y₀} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} → assocˡ ∘ ((f ⁂ g) ⁂ h) ≡ (f ⁂ (g ⁂ h)) ∘ assocˡ
  assocˡ-commute {f = f} {g} {h} =
    begin
      assocˡ ∘ ((f ⁂ g) ⁂ h)
    ≈⟨ ∘-resp-≡ˡ (prop assocˡ-convert) ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ ((f ⁂ g) ⁂ h)
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ ((f ⁂ g) ⁂ h) , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ ((f ⁂ g) ⁂ h) ⟩
    ≈⟨ ⟨⟩-cong₂ (glue π₁∘⁂ π₁∘⁂) ⟨⟩∘ ⟩
      ⟨ f ∘ (π₁ ∘ π₁) , ⟨ (π₂ ∘ π₁) ∘ ((f ⁂ g) ⁂ h) , π₂ ∘ ((f ⁂ g) ⁂ h) ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ refl (⟨⟩-cong₂ (glue π₂∘⁂ π₁∘⁂) π₂∘⁂) ⟩
      ⟨ f ∘ (π₁ ∘ π₁) , ⟨ g ∘ (π₂ ∘ π₁) , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ refl (sym ⁂∘⟨⟩) ⟩
      ⟨ f ∘ (π₁ ∘ π₁) , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym ⁂∘⟨⟩ ⟩
      (f ⁂ (g ⁂ h)) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym (∘-resp-≡ʳ (prop assocˡ-convert)) ⟩
      (f ⁂ (g ⁂ h)) ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv
    open GlueSquares C

  .assocʳ-commute : ∀ {X₀ Y₀ X₁ Y₁ X₂ Y₂} {f : X₀ ⇒ Y₀} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} → assocʳ ∘ (f ⁂ (g ⁂ h)) ≡ ((f ⁂ g) ⁂ h) ∘ assocʳ
  assocʳ-commute {f = f} {g} {h} =
    begin
      assocʳ ∘ (f ⁂ (g ⁂ h))
    ≈⟨ ∘-resp-≡ˡ (prop assocʳ-convert) ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ (f ⁂ (g ⁂ h))
    ≈⟨ ⟨⟩∘ ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ (f ⁂ (g ⁂ h)) , (π₂ ∘ π₂) ∘ (f ⁂ (g ⁂ h)) ⟩
    ≈⟨ ⟨⟩-cong₂ ⟨⟩∘ (glue π₂∘⁂ π₂∘⁂) ⟩
      ⟨ ⟨ π₁ ∘ (f ⁂ (g ⁂ h)) , (π₁ ∘ π₂) ∘ (f ⁂ (g ⁂ h)) ⟩ , h ∘ (π₂ ∘ π₂) ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-cong₂ π₁∘⁂ (glue π₁∘⁂ π₂∘⁂)) refl ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ (π₁ ∘ π₂) ⟩ , h ∘ (π₂ ∘ π₂) ⟩
    ≈⟨ ⟨⟩-cong₂ (sym ⁂∘⟨⟩) refl ⟩
      ⟨ (f ⁂ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ (π₂ ∘ π₂) ⟩
    ≈⟨ sym ⁂∘⟨⟩ ⟩
      ((f ⁂ g) ⁂ h) ∘ ⟨ ⟨ π₁ , (π₁ ∘ π₂) ⟩ , (π₂ ∘ π₂) ⟩
    ≈⟨ sym (∘-resp-≡ʳ (prop assocʳ-convert)) ⟩
      ((f ⁂ g) ⁂ h) ∘ assocʳ
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv
    open GlueSquares C

  -- The implicit x is actually used implicitly by the rest of the expression, so don't take it out,
  -- or Agda will complain about something referring to something to which it has no access.
  -- The connection between the mentioned x and the rest of the type is given by the caller way up
  -- there, so if that were not using these the triangle and pentagon laws would be yellow.
  .triangle : ∀ {x} → first π₁ ≡ second π₂ ∘ assocˡ
  triangle = 
    begin
      first π₁
    ≣⟨ ⁂-convert π₁ id ⟩
      ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (Equiv.refl) identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (Equiv.refl) commute₂) ⟩
      ⟨ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym second∘⟨⟩ ⟩
      (id ⁂ π₂) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym (∘-resp-≡ʳ (Equiv.prop assocˡ-convert)) ⟩
      second π₂ ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv    
