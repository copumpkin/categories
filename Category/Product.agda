{-# OPTIONS --universe-polymorphism #-}
module Category.Product where

open import Level
open import Category

open import Relation.Binary
open import Data.Product

Product : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product C D = record 
  { Obj = C.Obj × D.Obj
  ; Hom = λ x y → C.Hom (proj₁ x) (proj₁ y) × D.Hom (proj₂ x) (proj₂ y)
  ; _≡_ = λ f g → C._≡_ (proj₁ f) (proj₁ g) × D._≡_ (proj₂ f) (proj₂ g)
  ; _∘_ = λ f g → C._∘_ (proj₁ f) (proj₁ g) , D._∘_ (proj₂ f) (proj₂ g)
  ; id = C.id , D.id
  ; ∘-assoc = λ f g h → C.∘-assoc (proj₁ f) (proj₁ g) (proj₁ h) , D.∘-assoc (proj₂ f) (proj₂ g) (proj₂ h)
  ; identityˡ = λ f → (C.identityˡ (proj₁ f)) , D.identityˡ (proj₂ f)
  ; identityʳ = λ f → (C.identityʳ (proj₁ f)) , D.identityʳ (proj₂ f)
  ; ≡-equiv = record 
    { refl = IsEquivalence.refl C.≡-equiv , IsEquivalence.refl D.≡-equiv
    ; sym = λ f → IsEquivalence.sym C.≡-equiv (proj₁ f) , IsEquivalence.sym D.≡-equiv (proj₂ f)
    ; trans = λ f g → IsEquivalence.trans C.≡-equiv (proj₁ f) (proj₁ g) , IsEquivalence.trans D.≡-equiv (proj₂ f) (proj₂ g)
    }          
  ; ∘-resp-≡ = λ f h g i f≡g h≡i → C.∘-resp-≡ _ _ _ _ (proj₁ f≡g) (proj₁ h≡i) , D.∘-resp-≡ _ _ _ _ (proj₂ f≡g) (proj₂ h≡i)
  }
  where
  module C = Category C
  module D = Category D
