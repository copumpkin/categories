{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Arrow {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

arrow : Category _ _ _
arrow = record 
  { Obj = Obj′ 
  ; Hom = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; equiv = record 
    { refl = IsEquivalence.refl equiv , IsEquivalence.refl equiv
    ; sym = λ f → IsEquivalence.sym equiv (fst f) , IsEquivalence.sym equiv (snd f)
    ; trans = λ f g → IsEquivalence.trans equiv (fst f) (fst g) , IsEquivalence.trans equiv (snd f) (snd g)
    }
  ; ∘-resp-≡ = λ f≡h g≡i → ∘-resp-≡ (fst f≡h) (fst g≡i) , ∘-resp-≡ (snd f≡h) (snd g≡i)
  }
  where
  Obj′ = ∃₂ Hom

  Hom′ : Rel Obj′ _
  Hom′ (a , b , f) (c , d , g) = ∃₂′ (λ h i → CommutativeSquare f h i g)

  infixr 9 _∘′_
  infix  4 _≡′_

  _≡′_ : {A B : Obj′} → (f g : Hom′ A B) → Set _
  (f , h , pf₁) ≡′ (i , g , pf₂) = (f ≡ i) × (h ≡ g)

  _∘′_ : {A B C : Obj′} → Hom′ B C → Hom′ A B → Hom′ A C
  _∘′_ {a , a′ , x} {b , b′ , y} {c , c′ , z} (f , h , pf₁) (i , g , pf₂) = f ∘ i , h ∘ g , pf
    where
    .pf : (h ∘ g) ∘ x ≡ z ∘ (f ∘ i)
    pf = begin
           (h ∘ g) ∘ x
         ≈⟨ assoc ⟩
           h ∘ (g ∘ x)
         ≈⟨ ∘-resp-≡ʳ pf₂ ⟩
           h ∘ (y ∘ i)
         ≈⟨ sym assoc ⟩
           (h ∘ y) ∘ i
         ≈⟨ ∘-resp-≡ˡ pf₁ ⟩
           (z ∘ f) ∘ i
         ≈⟨ assoc  ⟩
           z ∘ (f ∘ i)
         ∎
      where 
      open IsEquivalence equiv
      open SetoidReasoning hom-setoid

  id′ : ∀ {A} → Hom′ A A
  id′ {_ , _ , f} = id , id , pf
    where
    .pf : id ∘ f ≡ f ∘ id
    pf = begin
           id ∘ f
         ≈⟨ identityˡ ⟩
           f
         ≈⟨ sym identityʳ ⟩
           f ∘ id
         ∎
      where 
      open IsEquivalence equiv
      open SetoidReasoning hom-setoid

  .assoc′ : ∀ {A B C D} {f : Hom′ A B} {g : Hom′ B C} {h : Hom′ C D} → (h ∘′ g) ∘′ f ≡′ h ∘′ (g ∘′ f)
  assoc′ = assoc , assoc