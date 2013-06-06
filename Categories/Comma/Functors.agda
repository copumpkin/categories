{-# OPTIONS --universe-polymorphism #-}
module Categories.Comma.Functors where

open import Categories.Category
open import Categories.Functor
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; zip; map)
open import Level
open import Relation.Binary using (Rel)
open import Categories.Support.EqReasoning

open import Categories.Comma
open import Categories.Product

πComma :
  ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
    → {A : Category o₁ ℓ₁ e₁}
    → {B : Category o₂ ℓ₂ e₂}
    → {C : Category o₃ ℓ₃ e₃}
    → (S : Functor B C) (T : Functor A C)
    → Functor (S ↓ T) (Product B A)
πComma {A = A} {B} {C} S T =
  record
    { F₀ = F₀′
    ; F₁ = F₁′
    ; identity = λ {X} → identity′ {X}
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → homomorphism′ {X} {Y} {Z} {f} {g}
    ; F-resp-≡ = λ {X Y F G} pf → F-resp-≡′ {X} {Y} {F} {G} pf
    }
  where
    module A = Category A
    module B = Category B
    module C = Category C
    module S↓T = Category (S ↓ T)
    module B×A = Category (Product B A)
    module S = Functor S
    module T = Functor T
    open Comma S T using (_,_[_]) renaming (_,_,_ to ⟨_,_,_⟩)

    F₀′ : Comma.Obj′ S T → Category.Obj (Product B A)
    F₀′ ⟨ α , β , f ⟩ = α , β

    F₁′ : ∀ {X Y} → (S ↓ T) [ X , Y ] → Product B A [ F₀′ X , F₀′ Y ]
    F₁′ (g , h [ commutes ]) = g , h

    .identity′ : ∀ {X} → Product B A [ F₁′ (S↓T.id {X}) ≡ B×A.id ]
    identity′ {X} = Category.Equiv.refl B , Category.Equiv.refl A

    .homomorphism′ : ∀ {X Y Z} {f : (S ↓ T) [ X , Y ]} {g : (S ↓ T) [ Y , Z ]}
                     → Product B A [ F₁′ ((S ↓ T) [ g ∘ f ]) ≡ Product B A [ F₁′ g ∘ F₁′ f ] ]
    homomorphism′ {X} {Y} {Z} {fg , fh [ fcommutes ]} {gg , gh [ gcommutes ]} = (Category.Equiv.refl B) , (Category.Equiv.refl A)

    .F-resp-≡′ : ∀ {X Y} {F G : (S ↓ T) [ X , Y ]} → (S ↓ T) [ F ≡ G ] → Product B A [ F₁′ F ≡ F₁′ G ]
    F-resp-≡′ {X} {Y} {F} {G} pf = pf
