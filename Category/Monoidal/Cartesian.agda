{-# OPTIONS --universe-polymorphism #-}
module Category.Monoidal.Cartesian where

open import Support hiding (⊤; ⟨_,_⟩) renaming (_×_ to _×′_)
open import Category
open import Category.Monoidal
open import Category.Object.BinaryProducts
open import Category.Object.Products
open import Category.Object.Terminal
open import Category.Bifunctor using (Bifunctor)
open import Category.Morphisms

module AbstractProducts {o ℓ e : Level} (C : Category o ℓ e) (Ps : Products C) where
  private open Products C Ps renaming (terminal to T₀; binary to P₀)
  private module P₀ = BinaryProducts C P₀
  private module T₀ = Terminal C T₀
  open P₀ public using (_×_; π₁; π₂)
  open T₀ public using (⊤; !; !-unique; ⊤-id)
  private open Category.Category C
  private import Category.Object.Product as Product

  mutual
    first : ∀ {A B C} → (A ⇒ B) → ((A × C) ⇒ (B × C))
    first f = f ⁂ id

    second : ∀ {A C D} → (C ⇒ D) → ((A × C) ⇒ (A × D))
    second g = id ⁂ g

    abstract
      infix 10 _⁂_

      _⁂_ : ∀ {A B C D} → (A ⇒ B) → (C ⇒ D) → ((A × C) ⇒ (B × D))
      _⁂_ = P₀._⁂_

      ⟨_,_⟩ : ∀ {A B Q} → (Q ⇒ A) → (Q ⇒ B) → (Q ⇒ (A × B))
      ⟨_,_⟩ = P₀.⟨_,_⟩

      ⁂-convert : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → f ⁂ g ≣ ⟨ f ∘ π₁ , g ∘ π₂ ⟩
      ⁂-convert f g = ≣-refl

      assocˡ : ∀ {A B C} → (((A × B) × C) ⇒ (A × (B × C)))
      assocˡ = P₀.assocˡ

      assocˡ-convert : ∀ {A B C} → assocˡ {A} {B} {C} ≣ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      assocˡ-convert = ≣-refl

      assocʳ : ∀ {A B C} → ((A × (B × C)) ⇒ ((A × B) × C))
      assocʳ = P₀.assocʳ

      .assoc-iso : ∀ {A B C′} → Iso C (assocʳ {A} {B} {C′}) assocˡ
      assoc-iso = _≅_.iso C P₀.×-assoc

      .⁂∘⁂ : ∀ {A B C D E F} → {f : B ⇒ C} → {f′ : A ⇒ B} {g : E ⇒ F} {g′ : D ⇒ E} → (f ⁂ g) ∘ (f′ ⁂ g′) ≡ (f ∘ f′) ⁂ (g ∘ g′)
      ⁂∘⁂ = P₀.⁂∘⁂

      .⁂∘⟨⟩ : ∀ {A B C D E} → {f : B ⇒ C} {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g ∘ g′ ⟩
      ⁂∘⟨⟩ = P₀.⁂∘⟨⟩

      .⟨⟩-cong₂ : ∀ {A B C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
      ⟨⟩-cong₂ = P₀.⟨⟩-cong₂

      .⟨⟩∘ : ∀ {A B C D} {f : A ⇒ B} {g : A ⇒ C} {q : D ⇒ A} → ⟨ f , g ⟩ ∘ q ≡ ⟨ f ∘ q , g ∘ q ⟩
      ⟨⟩∘ = P₀.⟨⟩∘

      .first∘⟨⟩ : ∀ {A B C D} → {f : B ⇒ C} {f′ : A ⇒ B} {g′ : A ⇒ D} → first f ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f ∘ f′ , g′ ⟩
      first∘⟨⟩ = P₀.first∘⟨⟩

      .second∘⟨⟩ : ∀ {A B D E} → {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} → second g ∘ ⟨ f′ , g′ ⟩ ≡ ⟨ f′ , g ∘ g′ ⟩
      second∘⟨⟩ = P₀.second∘⟨⟩

      .η : ∀ {A B} → ⟨ π₁ , π₂ ⟩ ≡ id {A × B}
      η = P₀.η

      .commute₁ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
      commute₁ = P₀.commute₁

      .commute₂ : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
      commute₂ = P₀.commute₂

      .universal : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ (A × B)}
                   → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i
      universal = P₀.universal

Cartesian : ∀ {o ℓ e} (C : Category o ℓ e) → Products C → Monoidal C
Cartesian C Ps = record
  { ⊗ = ⊗
  ; id = ⊤
  ; identityˡ = record
    { F⇒G = record
      { η = λ X → π₂
      ; commute = λ f → Equiv.trans (prop (≣-cong (_∘_ π₂) (⁂-convert id (f zero)))) commute₂
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
      ; commute = λ f → Equiv.trans (prop (≣-cong (_∘_ π₁) (⁂-convert (f zero) id))) commute₁
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
      ; commute = {!!}
      }
    ; iso = λ X → record
      { isoˡ = Iso.isoʳ C assoc-iso
      ; isoʳ = Iso.isoˡ C assoc-iso
      }
    }
  ; triangle = λ {X} → triangle {X}
  ; pentagon = λ {X} → pentagon {X}
  }
  where
  open Category.Category C
  open AbstractProducts C Ps

  .prop : ∀ {A B : Obj} {f g : A ⇒ B} → f ≣ g → f ≡ g
  prop ≣-refl = Equiv.refl

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
      ≈⟨ prop (⁂-convert id id) ⟩
        ⟨ id ∘ π₁ , id ∘ π₂ ⟩
      ≈⟨ universal (id-comm {f = π₁}) (id-comm {f = π₂}) ⟩
        Category.id C
      ∎
      where open SetoidReasoning hom-setoid
    .F-resp-≡ : ∀ {A B F G} F≡G → _
    F-resp-≡ {F = F} {G} x = 
      begin
        fst F ⁂ snd F
      ≈⟨ prop (⁂-convert (fst F) (snd F)) ⟩
        ⟨ fst F ∘ π₁ , snd F ∘ π₂ ⟩
      ≈⟨ ⟨⟩-cong₂ (∘-resp-≡ˡ (fst x)) (∘-resp-≡ˡ (snd x)) ⟩
        ⟨ fst G ∘ π₁ , snd G ∘ π₂ ⟩
      ≈⟨ prop (≣-sym (⁂-convert (fst G) (snd G))) ⟩
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
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      {!!}
    ≈⟨ {!!} ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ g ∘ (π₂ ∘ π₁) , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (Category.assoc C) (sym ⁂∘⟨⟩) ⟩
      ⟨ f ∘ (π₁ ∘ π₁) , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym ⁂∘⟨⟩ ⟩
      (f ⁂ (g ⁂ h)) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym (∘-resp-≡ʳ (prop assocˡ-convert)) ⟩
      (f ⁂ (g ⁂ h)) ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open Equiv

  -- The implicit x is actually used implicitly by the rest of the expression, so don't take it out,
  -- or Agda will complain about something referring to something to which it has no access.
  -- The connection between the mentioned x and the rest of the type is given by the caller way up
  -- there, so if that were not using these the triangle and pentagon laws would be yellow.
  .triangle : ∀ {x} → first π₁ ≡ second π₂ ∘ assocˡ
  triangle = 
    begin
      first π₁
    ≈⟨ prop (⁂-convert π₁ id) ⟩
      ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (IsEquivalence.refl equiv) identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ≈⟨ sym (⟨⟩-cong₂ (IsEquivalence.refl equiv) commute₂) ⟩
      ⟨ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym second∘⟨⟩ ⟩
      (id ⁂ π₂) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ sym (prop (≣-cong (_∘_ (second π₂)) assocˡ-convert)) ⟩
      second π₂ ∘ assocˡ
    ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv    

{-
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
  pentagon {x} = {!!}