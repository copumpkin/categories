{-# OPTIONS --universe-polymorphism #-}

open import Support
open import Category

module Category.Slice {o ℓ e} (C : Category o ℓ e) where

open Category.Category C

slice : Obj → Category _ _ _
slice x = record 
  { Obj = Obj′
  ; Hom = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record 
    { refl = IsEquivalence.refl equiv
    ; sym = IsEquivalence.sym equiv
    ; trans = IsEquivalence.trans equiv
    }
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} → ∘-resp-≡′ {f = f} {h} {g} {i}
  }
  where
  Obj′ = ∃ (λ y → Hom y x)

  Hom′ : Rel Obj′ _
  Hom′ (b , f) (c , g) = ∃′ (λ h → g ∘ h ≡ f)

  infixr 9 _∘′_
  infix  4 _≡′_

  _≡′_ : ∀ {A B} → Rel (Hom′ A B) _
  (f , pf₁) ≡′ (g , pf₂) = f ≡ g

  _∘′_ : ∀ {a b c} → Hom′ b c → Hom′ a b → Hom′ a c
  _∘′_ {a , a⇒x} {b , b⇒x} {c , c⇒x} (b⇒c , pf₁) (a⇒b , pf₂) = b⇒c ∘ a⇒b , pf
    where
    .pf : c⇒x ∘ (b⇒c ∘ a⇒b) ≡ a⇒x
    pf = begin
           c⇒x ∘ (b⇒c ∘ a⇒b)
         ≈⟨ sym assoc ⟩
           (c⇒x ∘ b⇒c) ∘ a⇒b
         ≈⟨ ∘-resp-≡ˡ pf₁ ⟩
           b⇒x ∘ a⇒b
         ≈⟨ pf₂ ⟩
           a⇒x
         ∎
      where 
      open IsEquivalence equiv
      open SetoidReasoning hom-setoid

  id′ : {A : Obj′} -> Hom′ A A
  id′ = id , identityʳ

  .assoc′ : {A B C D : Obj′} {f : Hom′ A B} {g : Hom′ B C} {h : Hom′ C D}
         → (h ∘′ g) ∘′ f ≡′ h ∘′ (g ∘′ f)
  assoc′ = assoc

  .∘-resp-≡′ :  {A B C : Obj′} {f h : Hom′ B C} {g i : Hom′ A B}
           → f ≡′ h 
           → g ≡′ i 
           → f ∘′ g ≡′ h ∘′ i
  ∘-resp-≡′ f≡h g≡i = ∘-resp-≡ f≡h g≡i
