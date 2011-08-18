{-# OPTIONS --universe-polymorphism #-}
module Categories.Comma where

open import Categories.Category
open import Categories.Functor
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; zip; map)
open import Level
open import Relation.Binary using (Rel)
open import Categories.Support.EqReasoning

Comma :
    {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level}
    {A : Category o₁ ℓ₁ e₁}
    {B : Category o₂ ℓ₂ e₂}
    {C : Category o₃ ℓ₃ e₃}
    → Functor A C → Functor B C
    → Category (o₁ ⊔ o₂ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₂ ⊔ e₃) (e₁ ⊔ e₂)
Comma {o₁}{ℓ₁}{e₁}
      {o₂}{ℓ₂}{e₂}
      {o₃}{ℓ₃}{e₃}
      {A}{B}{C} T S
  = record
  { Obj         = Obj′
  ; _⇒_         = Hom′
  ; _≡_         = _≡′_
  ; _∘_         = _∘′_
  ; id          = id′
  ; assoc       = A.assoc , B.assoc
  ; identityˡ   = A.identityˡ , B.identityˡ
  ; identityʳ   = A.identityʳ , B.identityʳ
  ; equiv = record 
    { refl  = A.Equiv.refl , B.Equiv.refl
    ; sym   = map A.Equiv.sym B.Equiv.sym
    ; trans = zip A.Equiv.trans B.Equiv.trans
    }          
  ; ∘-resp-≡    = zip A.∘-resp-≡ B.∘-resp-≡
  } where
    module A = Category A
    module B = Category B
    module C = Category C
    module T = Functor T
    module S = Functor S
    
    open T using () renaming (F₀ to T₀; F₁ to T₁)
    open S using () renaming (F₀ to S₀; F₁ to S₁)
    
    infixr 9 _∘′_
    infix  4 _≡′_
    
    record Obj′ : Set (o₁ ⊔ o₂ ⊔ ℓ₃) where
        constructor _,_,_
        field
            α : A.Obj
            β : B.Obj
            f : C [ T₀ α , S₀ β ]
    
    record Hom′ (X₁ X₂ : Obj′) : Set (ℓ₁ ⊔ ℓ₂ ⊔ e₃) where
        constructor _,_[_]
        open Obj′ X₁ renaming (α to α₁; β to β₁; f to f₁)
        open Obj′ X₂ renaming (α to α₂; β to β₂; f to f₂)
        
        field
            g         : A [ α₁ , α₂ ]
            h         : B [ β₁ , β₂ ]
            .commutes : C.CommutativeSquare f₁ (T₁ g) (S₁ h) f₂
    
    _≡′_ : ∀ {X₁ X₂} → Rel (Hom′ X₁ X₂) _
    (g₁ , h₁ [ _ ]) ≡′ (g₂ , h₂ [ _ ]) 
        = A [ g₁ ≡ g₂ ]
        × B [ h₁ ≡ h₂ ]
    
    id′ : {A : Obj′} → Hom′ A A
    id′ { A } = record 
        { g = A.id ; h = B.id
        ; commutes = 
            begin
                C [ S₁ B.id ∘ f ]
            ↓⟨ S.identity ⟩∘⟨ refl ⟩
                C [ C.id ∘ f ]
            ↓⟨ C.identityˡ ⟩
                f
            ↑⟨ C.identityʳ ⟩
                C [ f ∘ C.id ]
            ↑⟨ refl ⟩∘⟨ T.identity ⟩
                C [ f ∘ T₁ A.id ]
            ∎
        } where
            open Obj′ A
            open C.HomReasoning
            open C.Equiv
    
    _∘′_ : ∀ {X₁ X₂ X₃} → Hom′ X₂ X₃ → Hom′ X₁ X₂ → Hom′ X₁ X₃
    _∘′_ {X₁}{X₂}{X₃} (g₁ , h₁ [ commutes₁ ]) (g₂ , h₂ [ commutes₂ ])
        = A [ g₁ ∘ g₂ ] , B [ h₁ ∘ h₂ ]
        [ begin
            -- commutes₁ : C [ C [ S₁ h₁ ∘ f₂ ]  ≡ C [ f₃ ∘ T₁ g₁ ] ]
            -- commutes₂ : C [ C [ S₁ h₂ ∘ f₁ ]  ≡ C [ f₂ ∘ T₁ g₂ ] ]
                C [ S₁ (B [ h₁ ∘ h₂ ]) ∘ f₁ ]
            ↓⟨ S.homomorphism ⟩∘⟨ refl ⟩
                C [ C [ S₁ h₁ ∘ S₁ h₂ ] ∘ f₁ ]
            ↓⟨ C.assoc ⟩
                C [ S₁ h₁ ∘  C [ S₁ h₂ ∘ f₁ ] ]
            ↓⟨ refl ⟩∘⟨ commutes₂ ⟩
                C [ S₁ h₁ ∘  C [ f₂ ∘ T₁ g₂ ] ]
            ↑⟨ C.assoc ⟩
                C [ C [ S₁ h₁ ∘  f₂ ] ∘ T₁ g₂ ]
            ↓⟨ commutes₁ ⟩∘⟨ refl ⟩
                C [ C [ f₃ ∘ T₁ g₁ ] ∘ T₁ g₂ ]
            ↓⟨ C.assoc ⟩
                C [ f₃ ∘ C [ T₁ g₁ ∘ T₁ g₂ ] ]
            ↑⟨ refl ⟩∘⟨ T.homomorphism ⟩
                C [ f₃ ∘ T₁ (A [ g₁ ∘ g₂ ]) ]
         ∎ ]
        where
            open C.HomReasoning
            open C.Equiv
            open Obj′ X₁ renaming (α to α₁; β to β₁; f to f₁)
            open Obj′ X₂ renaming (α to α₂; β to β₂; f to f₂)
            open Obj′ X₃ renaming (α to α₃; β to β₃; f to f₃)

_↓_ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
      → {A : Category o₁ ℓ₁ e₁}
      → {B : Category o₂ ℓ₂ e₂}
      → {C : Category o₃ ℓ₃ e₃}
      → (S : Functor B C) (T : Functor A C)
      → Category _ _ _
T ↓ S = Comma T S