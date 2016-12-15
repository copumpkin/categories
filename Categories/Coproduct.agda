{-# OPTIONS --universe-polymorphism #-}
module Categories.Coproduct where

open import Level
open import Data.Empty
open import Data.Sum
open import Relation.Binary.Core

open import Categories.Category

module _ {a a′ ℓ ℓ′} {A : Set a} (_∼_ : Rel A ℓ) where
  lift-∼ : Rel (Lift {ℓ = a′} A) (ℓ ⊔ ℓ′)
  lift-∼ (lift x) (lift y) = Lift {ℓ = ℓ′} (x ∼ y)

  lift-equiv : IsEquivalence _∼_ → IsEquivalence lift-∼
  lift-equiv record { refl = refl-∼ ; sym = sym-∼ ; trans = trans-∼ } =
    record { refl = lift refl-∼
           ; sym = λ { {lift x} {lift y} {lift x∼y} → lift (sym-∼ x∼y) }
           ; trans = λ { {lift x} {lift y} {lift z} {lift x∼y} {lift y∼z} → lift (trans-∼ x∼y y∼z) }
           }

Coproduct : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Coproduct {o} {ℓ} {e} {o′} {ℓ′} {e′} C D = record
  { Obj = C.Obj ⊎ D.Obj
  ; _⇒_ = λ { (inj₁ c₁) (inj₁ c₂) → Lift {ℓ = ℓ′} (C._⇒_ c₁ c₂)
             ; (inj₁ _)  (inj₂ _)  → Lift ⊥
             ; (inj₂ _)  (inj₁ _)  → Lift ⊥
             ; (inj₂ d₁) (inj₂ d₂) → Lift {ℓ = ℓ} (D._⇒_ d₁ d₂)
             }
  ; _≡_ = λ { {inj₁ _} {inj₁ _} → lift-∼ {ℓ′ = e′} C._≡_
            ; {inj₁ _} {inj₂ _} (lift ()) (lift ())
            ; {inj₂ _} {inj₁ _} (lift ()) (lift ())
            ; {inj₂ _} {inj₂ _} → lift-∼ {ℓ′ = e} D._≡_
            }
  ; _∘_ = λ { {inj₁ _} {inj₁ _} {inj₁ _} (lift f) (lift g) → lift (C._∘_ f g)
            ; {inj₁ _} {inj₁ _} {inj₂ _} (lift ()) _
            ; {inj₁ _} {inj₂ _} {inj₁ _} _ (lift ())
            ; {inj₁ _} {inj₂ _} {inj₂ _} _ (lift ())
            ; {inj₂ _} {inj₁ _} {inj₁ _} _ (lift ())
            ; {inj₂ _} {inj₁ _} {inj₂ _} (lift ()) _
            ; {inj₂ _} {inj₂ _} {inj₁ _} (lift ()) _
            ; {inj₂ _} {inj₂ _} {inj₂ _} (lift f) (lift g) → lift (D._∘_ f g)
            }
  ; id = λ { {inj₁ _} → lift C.id ; {inj₂ _} → lift D.id }
  ; assoc = λ { {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} → lift C.assoc
              ; {inj₁ _} {inj₁ _} {inj₁ _} {inj₂ _} {_} {_} {lift ()}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₁ _} {_} {lift ()} {_}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₂ _} {_} {lift ()} {_}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₁ _} {_} {lift ()} {_}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₂ _} {_} {lift ()} {_}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₁ _} {_} {_} {lift ()}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} → lift D.assoc
              }
  ; identityˡ = λ { {inj₁ _} {inj₁ _} → lift C.identityˡ
                  ; {inj₁ _} {inj₂ _} {lift ()}
                  ; {inj₂ _} {inj₁ _} {lift ()}
                  ; {inj₂ _} {inj₂ _} → lift D.identityˡ
                  }
  ; identityʳ = λ { {inj₁ _} {inj₁ _} → lift C.identityʳ
                  ; {inj₁ _} {inj₂ _} {lift ()}
                  ; {inj₂ _} {inj₁ _} {lift ()}
                  ; {inj₂ _} {inj₂ _} → lift D.identityʳ
                  }
  ; equiv = λ { {inj₁ _} {inj₁ _} → lift-equiv _ C.equiv
              ; {inj₁ _} {inj₂ _} → record { refl = λ { {lift ()} }
                                           ; sym = λ { {lift ()} }
                                           ; trans = λ { {lift ()} }
                                           }
              ; {inj₂ _} {inj₁ _} → record { refl = λ { {lift ()} }
                                           ; sym = λ { {lift ()} }
                                           ; trans = λ { {lift ()} }
                                           }
              ; {inj₂ _} {inj₂ _} → lift-equiv _ D.equiv
              }
  ; ∘-resp-≡ = λ { {inj₁ _} {inj₁ _} {inj₁ _} → λ { (lift f) (lift g) → lift (C.∘-resp-≡ f g) }
                 ; {inj₁ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
                 ; {inj₁ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
                 ; {inj₁ _} {inj₂ _} {inj₂ _} {_} {_} {lift ()}
                 ; {inj₂ _} {inj₁ _} {inj₁ _} {_} {_} {lift ()}
                 ; {inj₂ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
                 ; {inj₂ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
                 ; {inj₂ _} {inj₂ _} {inj₂ _} → λ { (lift f) (lift g) → lift (D.∘-resp-≡ f g) }
                 }
  }
  where
  module C = Category C
  module D = Category D
