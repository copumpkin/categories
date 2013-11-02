{-# OPTIONS --universe-polymorphism #-}
module Categories.FunctorCategory where

open import Data.Product

open import Categories.Category
import Categories.Functor as Cat
open import Categories.Functor hiding (equiv; id; _∘_; _≡_)
open import Categories.NaturalTransformation
open import Categories.Product
open import Categories.Square

Functors : ∀ {o ℓ e} {o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Category _ _ _
Functors C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≡_ = _≡_
  ; _∘_ = _∘₁_
  ; id = id
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc₁ {X = f} {g} {h}
  ; identityˡ = λ {_} {_} {f} → identity₁ˡ {X = f}
  ; identityʳ = λ {_} {_} {f} → identity₁ʳ {X = f}
  ; equiv = λ {F} {G} → equiv {F = F} {G = G}
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} → ∘₁-resp-≡ {f = f} {h} {g} {i}
  }


eval : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e}{D : Category o′ ℓ′ e′} → Functor (Product (Functors C D) C) D
eval {C = C} {D = D} = 
    record {
      F₀ = λ x → let F , c = x in F₀ F c;
      F₁ = λ { {F , c₁} {G , c₂} (ε , f) → F₁ G f D.∘ η ε _};
      identity = λ { {F , c} → begin
                                 F₁ F C.id D.∘ D.id ↓⟨ D.identityʳ ⟩
                                 F₁ F C.id          ↓⟨ identity F ⟩ 
                                 D.id               ∎};
      homomorphism = λ { {F , c₁} {G , c₂} {H , c₃} {ε₁ , f₁} {ε₂ , f₂} → 
         begin
           F₁ H (f₂ C.∘ f₁) D.∘ η ε₂ c₁ D.∘ η ε₁ c₁        ↑⟨ D.assoc ⟩
           (F₁ H (f₂ C.∘ f₁) D.∘ η ε₂ c₁) D.∘ η ε₁ c₁ 
              ↓⟨ D.∘-resp-≡ˡ (begin
                                F₁ H (C [ f₂ ∘ f₁ ]) D.∘ η ε₂ c₁  ↓⟨ D.∘-resp-≡ˡ (homomorphism H) ⟩
                                (F₁ H f₂ D.∘ F₁ H f₁) D.∘ η ε₂ c₁ ↓⟨ D.assoc ⟩
                                F₁ H f₂ D.∘ F₁ H f₁ D.∘ η ε₂ c₁   ↑⟨ D.∘-resp-≡ʳ (commute ε₂ f₁) ⟩ 
                                F₁ H f₂ D.∘ η ε₂ c₂ D.∘ F₁ G f₁   ↑⟨ D.assoc ⟩ 
                                (F₁ H f₂ D.∘ η ε₂ c₂) D.∘ F₁ G f₁ ∎)
               ⟩
           ((F₁ H f₂ D.∘ η ε₂ c₂) D.∘ F₁ G f₁) D.∘ η ε₁ c₁ ↓⟨ D.assoc ⟩
           (F₁ H f₂ D.∘ η ε₂ c₂) D.∘ F₁ G f₁ D.∘ η ε₁ c₁   ∎ };
      F-resp-≡ = λ { {F , c₁} {G , c₂} {ε₁ , f₁} {ε₂ , f₂} (ε₁≡ε₂ , f₁≡f₂)
                        → D.∘-resp-≡ (F-resp-≡ G f₁≡f₂) ε₁≡ε₂} }
  where
    module C = Category C
    module D = Category D
    
    open Functor
    open NaturalTransformation
    open D.HomReasoning

Cat[-∘_] : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂}
             {C : Category o₃ ℓ₃ e₃} -> Functor A B -> Functor (Functors B C) (Functors A C)
Cat[-∘_] {C = C} r = record 
  { F₀ = λ X → X Cat.∘ r
  ; F₁ = λ η → η ∘ʳ r
  ; identity = C.Equiv.refl
  ; homomorphism = C.Equiv.refl
  ; F-resp-≡ = λ x → x 
  }
 where
   module C = Category C
