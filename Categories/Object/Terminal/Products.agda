{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category
open import Categories.Object.Terminal
open import Level

module Categories.Object.Terminal.Products {o ℓ e : Level}
    (C : Category o ℓ e)
    (T : Terminal C) where

open import Categories.Object.Product

open Category C
open Terminal T

[⊤×⊤] : Obj
[⊤×⊤] = ⊤

[⊤×⊤]-product : Product C ⊤ ⊤
[⊤×⊤]-product = record
    { A×B       = [⊤×⊤]
    ; π₁        = !
    ; π₂        = !
    ; ⟨_,_⟩     = λ _ _ → !
    ; commute₁  = !-unique₂ _ _
    ; commute₂  = !-unique₂ _ _
    ; universal = λ _ _ → !-unique _
    }

[⊤×_] : Obj → Obj
[⊤× X ] = X

[⊤×_]-product : (X : Obj) → Product C ⊤ X
[⊤×_]-product X = record
    { A×B       = [⊤× X ]
    ; π₁        = !
    ; π₂        = id
    ; ⟨_,_⟩     = λ _ f → f
    ; commute₁  = !-unique₂ _ _
    ; commute₂  = identityˡ
    ; universal = λ {A}{f}{g}{i} _ id∘i≡g → 
        begin
            g
        ↑⟨ id∘i≡g ⟩ 
            id ∘ i
        ↓⟨ identityˡ ⟩
            i
        ∎
    } where open HomReasoning

[_×⊤] : Obj → Obj
[ X ×⊤] = X

[_×⊤]-product : (X : Obj) → Product C X ⊤
[_×⊤]-product X = record
    { A×B       = [ X ×⊤]
    ; π₁        = id
    ; π₂        = !
    ; ⟨_,_⟩     = λ f _ → f
    ; commute₁  = identityˡ
    ; commute₂  = !-unique₂ _ _
    ; universal = λ {A}{f}{g}{i} id∘i≡f _ → 
        begin
            f
        ↑⟨ id∘i≡f ⟩ 
            id ∘ i
        ↓⟨ identityˡ ⟩
            i
        ∎
    } where open HomReasoning

