{-# OPTIONS --universe-polymorphism #-}
module Category.Product where

open import Support
open import Category

Product : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product C D = record 
  { Obj = C.Obj × D.Obj
  ; Hom = λ x y → C.Hom (fst x) (fst y) × D.Hom (snd x) (snd y)
  ; _≡_ = λ f g → C._≡_ (fst f) (fst g) × D._≡_ (snd f) (snd g)
  ; _∘_ = λ f g → C._∘_ (fst f) (fst g) , D._∘_ (snd f) (snd g)
  ; id = C.id , D.id
  ; assoc = C.assoc , D.assoc
  ; identityˡ = C.identityˡ , D.identityˡ
  ; identityʳ = C.identityʳ , D.identityʳ
  ; equiv = record 
    { refl = IsEquivalence.refl C.equiv , IsEquivalence.refl D.equiv
    ; sym = λ f → IsEquivalence.sym C.equiv (fst f) , IsEquivalence.sym D.equiv (snd f)
    ; trans = λ f g → IsEquivalence.trans C.equiv (fst f) (fst g) , IsEquivalence.trans D.equiv (snd f) (snd g)
    }          
  ; ∘-resp-≡ = λ f≡g h≡i → C.∘-resp-≡ (fst f≡g) (fst h≡i) , D.∘-resp-≡ (snd f≡g) (snd h≡i)
  }
  where
  module C = Category.Category C
  module D = Category.Category D

open import Category.Functor using (Functor)

preassoc : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃} (C : Category o₁ ℓ₁ e₁) (D : Category o₂ ℓ₂ e₂) (E : Category o₃ ℓ₃ e₃) → Functor (Product (Product C D) E) (Product C (Product D E))
preassoc C D E = record {
    F₀ = λ x → fst (fst x) , snd (fst x) , snd x
  ; F₁ = λ f → fst (fst f) , snd (fst f) , snd f
  ; identity = IsEquivalence.refl C.equiv , IsEquivalence.refl D.equiv , IsEquivalence.refl E.equiv
  ; homomorphism = IsEquivalence.refl C.equiv , IsEquivalence.refl D.equiv , IsEquivalence.refl E.equiv
  ; F-resp-≡ = λ F≡G → fst (fst F≡G) , snd (fst F≡G) , snd F≡G
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  module E = Category.Category E

infixr 2 _⁂_
_⁂_ : ∀ {o₁ ℓ₁ e₁ o′₁ ℓ′₁ e′₁ o₂ ℓ₂ e₂ o′₂ ℓ′₂ e′₂} {C₁ : Category o₁ ℓ₁ e₁} {D₁ : Category o′₁ ℓ′₁ e′₁} → {C₂ : Category o₂ ℓ₂ e₂} {D₂ : Category o′₂ ℓ′₂ e′₂} → (F₁ : Functor C₁ D₁) → (F₂ : Functor C₂ D₂) → Functor (Product C₁ C₂) (Product D₁ D₂)
F ⁂ G = record
        { F₀ = ⟨ F.F₀ , G.F₀ ⟩
        ; F₁ = ⟨ F.F₁ , G.F₁ ⟩
        ; identity = F.identity , G.identity
        ; homomorphism = F.homomorphism , G.homomorphism
        ; F-resp-≡ = ⟨ F.F-resp-≡ , G.F-resp-≡ ⟩ 
        }
        where
        module F = Category.Functor.Functor F
        module G = Category.Functor.Functor G