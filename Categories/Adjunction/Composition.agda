{-# OPTIONS --universe-polymorphism #-}
module Categories.Adjunction.Composition where

open import Level

open import Categories.Category
open import Categories.Functor hiding (equiv; assoc; identityˡ; identityʳ; ∘-resp-≡) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalTransformation hiding (equiv; setoid) renaming (id to idT; _≡_ to _≡T_)

open import Categories.Adjunction

infixr 9 _∘_
_∘_ : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
      {F : Functor D C} {G : Functor C D} {H : Functor E D} {I : Functor D E} →
      Adjunction F G → Adjunction H I → Adjunction (F ∘F H) (I ∘F G)
_∘_ {C = C} {D} {E} {F} {G} {H} {I} X Y = record
  { unit = (I ∘ˡ (Xη′ ∘ʳ H)) ∘₁ Yη′
  ; counit = Xε′ ∘₁ (F ∘ˡ (Yε′ ∘ʳ G))
  ; zig = λ {x} → zig′ {x}
  ; zag = λ {x} → zag′ {x}
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
    module I = Functor I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)
    module X′ = Adjunction X renaming (unit to Xη′; counit to Xε′)
    module Y′ = Adjunction Y renaming (unit to Yη′; counit to Yε′)
    module Xη = NaturalTransformation (Adjunction.unit X) renaming (η to ηX)
    module Yη = NaturalTransformation (Adjunction.unit Y) renaming (η to ηY)
    module Xε = NaturalTransformation (Adjunction.counit X) renaming (η to εX)
    module Yε = NaturalTransformation (Adjunction.counit Y) renaming (η to εY)
    open C
    open D
    open E
    open F
    open G
    open H
    open I
    open X′
    open Y′
    open Xη
    open Yη
    open Xε
    open Yε

    .zig′ : {x : E.Obj} →
              C.id C.≡
                (εX (F₀ (H₀ x)) C.∘ F₁ (εY (G₀ (F₀ (H₀ x))))) C.∘
                  F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
    zig′ {x} =
        begin
          C.id
        ↑⟨ F.identity ⟩
          F₁ D.id
        ↓⟨ F-resp-≡ Y′.zig ⟩
          F₁ (D [ εY (H₀ x) ∘ H₁ (ηY x) ])
        ↓⟨ F.homomorphism ⟩
          F₁ (εY (H₀ x)) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ˡ C.identityˡ ⟩
          (C.id C.∘ F₁ (εY (H₀ x))) C.∘
            F₁ (H₁ (ηY x))
        ↓⟨ C.∘-resp-≡ˡ (C.∘-resp-≡ˡ X′.zig) ⟩
          ((εX (F₀ (H₀ x)) C.∘ F₁ (ηX (H₀ x))) C.∘ F₁ (εY (H₀ x))) C.∘
            F₁ (H₁ (ηY x))
        ↓⟨ C.∘-resp-≡ˡ C.assoc ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (ηX (H₀ x)) C.∘ F₁ (εY (H₀ x))) C.∘
            F₁ (H₁ (ηY x))
        ↓⟨ C.assoc ⟩
          εX (F₀ (H₀ x)) C.∘ (F₁ (ηX (H₀ x)) C.∘ F₁ (εY (H₀ x))) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ (C.∘-resp-≡ˡ F.homomorphism) ⟩
          εX (F₀ (H₀ x)) C.∘ F₁ (ηX (H₀ x) D.∘ εY (H₀ x)) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ F.homomorphism ⟩
          εX (F₀ (H₀ x)) C.∘ F₁ ((ηX (H₀ x) D.∘ εY (H₀ x)) D.∘ H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (D.∘-resp-≡ˡ (Yε.commute (ηX (H₀ x))))) ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ ((εY (G₀ (F₀ (H₀ x))) D.∘ H₁ (I₁ (ηX (H₀ x)))) D.∘ H₁ (ηY x))
        ↓⟨ C.∘-resp-≡ʳ (F-resp-≡ D.assoc) ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ (εY (G₀ (F₀ (H₀ x))) D.∘ D [ H₁ (I₁ (ηX (H₀ x))) ∘ H₁ (ηY x) ])
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (D.∘-resp-≡ʳ H.homomorphism)) ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ (D [ εY (G₀ (F₀ (H₀ x))) ∘ H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x) ])
        ↓⟨ C.∘-resp-≡ʳ F.homomorphism ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ (εY (G₀ (F₀ (H₀ x)))) C.∘ F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.assoc ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (εY (G₀ (F₀ (H₀ x))))) C.∘
            F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
        ∎
      where open C.HomReasoning

    .zag′ : {x : C.Obj} →
              E.id E.≡
                I₁ (G₁ (εX x C.∘ F₁ (εY (G₀ x)))) E.∘
                I₁ (ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
    zag′ {x} =
        begin
          E.id
        ↓⟨ Y′.zag ⟩
          (I₁ (εY (G₀ x))) E.∘ (ηY (I₀ (G₀ x)))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ D.identityˡ) ⟩
          (I₁ (D.id D.∘ (εY (G₀ x)))) E.∘ (ηY (I₀ (G₀ x)))
        ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ X′.zag)) ⟩
          (I₁ ((G₁ (εX x) D.∘ (ηX (G₀ x))) D.∘ (εY (G₀ x)))) E.∘ (ηY (I₀ (G₀ x)))
        ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ D.assoc) ⟩
          I₁ (G₁ (εX x) D.∘ ηX (G₀ x) D.∘ εY (G₀ x)) E.∘ ηY (I₀ (G₀ x))
        ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ʳ (Xη.commute (εY (G₀ x))))) ⟩
          I₁ (G₁ (εX x) D.∘ G₁ (F₁ (εY (G₀ x))) D.∘ ηX (H₀ (I₀ (G₀ x)))) E.∘
            ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ D.assoc) ⟩
          I₁ (D [ G₁ (εX x) ∘ G₁ (F₁ (εY (G₀ x))) ] D.∘ ηX (H₀ (I₀ (G₀ x))))
            E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ G.homomorphism)) ⟩
          I₁ (D [ G₁ (εX x C.∘ F₁ (εY (G₀ x))) ∘ ηX (H₀ (I₀ (G₀ x))) ]) E.∘
            ηY (I₀ (G₀ x))
        ↓⟨ E.∘-resp-≡ˡ I.homomorphism ⟩
          (I₁ (G₁ (εX x C.∘ F₁ (εY (G₀ x)))) E.∘ I₁ (ηX (H₀ (I₀ (G₀ x))))) E.∘
            ηY (I₀ (G₀ x))
        ↓⟨ E.assoc ⟩
          I₁ (G₁ (εX x C.∘ F₁ (εY (G₀ x)))) E.∘
            I₁ (ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ∎
      where open E.HomReasoning
