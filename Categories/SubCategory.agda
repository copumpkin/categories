module Categories.SubCategory where

open import Categories.Category
open import Data.Product

sub-category : ∀ {o ℓ e o′ ℓ′} -> (C : Category o ℓ e) -> let module C = Category C in 
               {A : Set o′} (U : A -> C.Obj) (R : ∀ {a b} -> U a C.⇒ U b -> Set ℓ′) ->   
               (∀ {a} -> R (C.id {U a})) -> (∀ {a b c} {f : U b C.⇒ U c} {g : U a C.⇒ U b} -> R f -> R g -> R (f C.∘ g)) →
               Category _ _ _
sub-category C {A} U R Rid R∘ = record 
  { Obj = A
  ; _⇒_ = λ a b → Σ (U a C.⇒ U b) R
  ; _≡_ = λ f g → proj₁ f C.≡ proj₁ g
  ; id = C.id , Rid
  ; _∘_ = λ f g → (proj₁ f C.∘ proj₁ g) , R∘ (proj₂ f) (proj₂ g)
  ; assoc = C.assoc
  ; identityˡ = C.identityˡ
  ; identityʳ = C.identityʳ
  ; equiv = record 
      { refl = C.Equiv.refl
      ; sym = C.Equiv.sym
      ; trans = C.Equiv.trans 
      }
  ; ∘-resp-≡ = C.∘-resp-≡ 
  }
  where
    module C = Category C
