{-# OPTIONS --universe-polymorphism #-}
module Categories.FunctorCategory where

open import Data.Product

open import Categories.Support.PropositionalEquality

open import Categories.Category
import Categories.Functor as Cat
open import Categories.Functor hiding (equiv; id; _∘_; _≡_; promote)
open import Categories.NaturalTransformation
open import Categories.Product
open import Categories.Square

Functorsᵉ : ∀ {o a} {o′ a′} → Category o a → Category o′ a′ → EasyCategory _ _ _
Functorsᵉ C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≡_ = _≡_
  ; _∘_ = _∘₁_
  ; id = id
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc₁ {X = f} {g} {h}
  ; identityˡ = λ {_} {_} {f} → identity₁ˡ {X = f}
  ; identityʳ = λ {_} {_} {f} → identity₁ʳ {X = f}
  ; promote = promote
  ; REFL = ≣-refl
  }

Functors : ∀ {o a} {o′ a′} → Category o a → Category o′ a′ → Category _ _
Functors C D = EASY Functorsᵉ C D

Functors-rel : ∀ {o a} {o′ a′} (C : Category o a) (D : Category o′ a′) → EasyRel (Functors C D) _
Functors-rel C D = record { _≡_ = _≡_; promote = promote; REFL = ≣-refl }


eval : ∀ {o a} {o′ a′} {C : Category o a}{D : Category o′ a′} → Functor (Product (Functors C D) C) D
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
           (F₁ H f₂ D.∘ η ε₂ c₂) D.∘ F₁ G f₁ D.∘ η ε₁ c₁   ∎ }}
  where
    module C = Category C
    module D = Category D
    
    open Functor
    open NaturalTransformation
    open D.HomReasoning

Cat[-∘_] : ∀ {o₁ a₁ o₂ a₂ o₃ a₃} {A : Category o₁ a₁} {B : Category o₂ a₂}
             {C : Category o₃ a₃} -> Functor A B -> Functor (Functors B C) (Functors A C)
Cat[-∘_] {C = C} r = record 
  { F₀ = λ X → X Cat.∘ r
  ; F₁ = λ η → η ∘ʳ r
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  }
 where
   module C = Category C
