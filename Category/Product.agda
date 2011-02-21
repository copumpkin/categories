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
