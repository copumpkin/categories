{-# OPTIONS --universe-polymorphism #-}
module Categories.Adjunction where

open import Level

open import Relation.Binary using (Rel; IsEquivalence)
open import Data.Sum
open import Data.Product
open import Function using (flip)

open import Categories.Category
open import Categories.Functor hiding (equiv; assoc; identityˡ; identityʳ; ∘-resp-≡) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalTransformation hiding (equiv; setoid) renaming (id to idT; _≡_ to _≡T_)
open import Categories.Monad
open import Categories.Support.Equivalence

record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} (F : Functor D C) (G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
  field
    unit   : NaturalTransformation idF (G ∘F F)
    counit : NaturalTransformation (F ∘F G) idF

    .zig : idT ≡T (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : idT ≡T (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

  private module C = Category C
  private module D = Category D

  private module F = Functor F
  private module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open F hiding (op)
  open G hiding (op)

  private module unit   = NaturalTransformation unit
  private module counit = NaturalTransformation counit

  monad : Monad D
  monad = record
    { F = G ∘F F
    ; η = unit
    ; μ = G ∘ˡ (counit ∘ʳ F)
    ; assoc = assoc′
    ; identityˡ = identityˡ′
    ; identityʳ = identityʳ′
    }
    where

    .assoc′ : ∀ {x}
           → G₁ (counit.η (F₀ x)) D.∘ G₁ (F₁ (G₁ (counit.η (F₀ x)))) D.≡ G₁ (counit.η (F₀ x)) D.∘ G₁ (counit.η (F₀ (G₀ (F₀ x))))
    assoc′ {x} =
        begin
          G₁ (counit.η (F₀ x)) D.∘ G₁ (F₁ (G₁ (counit.η (F₀ x))))
        ↑⟨ G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) C.∘ (F₁ (G₁ (counit.η (F₀ x)))))
        ↓⟨ G-resp-≡ (NaturalTransformation.commute counit (counit.η (F₀ x))) ⟩
          G₁ (counit.η (F₀ x) C.∘ counit.η (F₀ (G₀ (F₀ x))))
        ↓⟨ G.homomorphism ⟩
          G₁ (counit.η (F₀ x)) D.∘ G₁ (counit.η (F₀ (G₀ (F₀ x))))
        ∎
      where
      open D.HomReasoning

    .identityˡ′ : ∀ {x} → G₁ (counit.η (F₀ x)) D.∘ G₁ (F₁ (unit.η x)) D.≡ D.id
    identityˡ′ {x} =
        begin
          G₁ (counit.η (F₀ x)) D.∘ G₁ (F₁ (unit.η x))
        ↑⟨ G.homomorphism ⟩
          G₁ ((counit.η (F₀ x)) C.∘ (F₁ (unit.η x)))
        ↑⟨ G-resp-≡ zig ⟩
          G₁ C.id
        ↓⟨ G.identity ⟩
          D.id
        ∎
      where
      open D.HomReasoning

    .identityʳ′ : ∀ {x} → G₁ (counit.η (F₀ x)) D.∘ unit.η (G₀ (F₀ x)) D.≡ D.id
    identityʳ′ = D.Equiv.sym zag

  op : Adjunction {C = D.op} {D = C.op} G.op F.op
  op = record { unit = counit.op; counit = unit.op; zig = zag; zag = zig }

infixr 5 _⊣_
_⊣_ = Adjunction

id : ∀ {o ℓ e} {C : Category o ℓ e} → Adjunction (idF {C = C}) (idF {C = C})
id {C = C} = record
   { unit = idT
   ; counit = idT
   ; zig = Equiv.sym C.identityˡ
   ; zag = Equiv.sym C.identityˡ
   }
  where
    module C = Category C
    open C

infixr 9 _∘_
_∘_ : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
      {F : Functor D C} {G : Functor C D} {H : Functor E D} {I : Functor D E} →
      Adjunction F G → Adjunction H I → Adjunction (F ∘F H) (I ∘F G)
_∘_ {C = C} {D} {E} {F} {G} {H} {I} X Y = record
  { unit = (I ∘ˡ (Xη' ∘ʳ H)) ∘₁ Yη'
  ; counit = Xε' ∘₁ (F ∘ˡ (Yε' ∘ʳ G))
  ; zig = λ {x} → zig' {x}
  ; zag = λ {x} → zag' {x}
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
    module I = Functor I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)
    private module X' = Adjunction X renaming (unit to Xη'; counit to Xε')
    private module Y' = Adjunction Y renaming (unit to Yη'; counit to Yε')
    private module Xη = NaturalTransformation (Adjunction.unit X) renaming (η to ηX)
    private module Yη = NaturalTransformation (Adjunction.unit Y) renaming (η to ηY)
    private module Xε = NaturalTransformation (Adjunction.counit X) renaming (η to εX)
    private module Yε = NaturalTransformation (Adjunction.counit Y) renaming (η to εY)
    open C
    open D
    open E
    open F
    open G
    open H
    open I
    open X'
    open Y'
    open Xη
    open Yη
    open Xε
    open Yε

    .zig' : {x : E.Obj} →
              NaturalTransformation.η idT x C.≡
                NaturalTransformation.η
                (((Xε' ∘₁ (F ∘ˡ (Yε' ∘ʳ G))) ∘ʳ (F ∘F H)) ∘₁
                 ((F ∘F H) ∘ˡ ((I ∘ˡ (Xη' ∘ʳ H)) ∘₁ Yη')))
                x
    zig' {x} = {!!} {-
        begin
          C.id
        ↑⟨ F.identity ⟩
          F₁ D.id
        ↓⟨ F-resp-≡ Y'.zig ⟩
          F₁ (D [ εY (H₀ x) ∘ H₁ (ηY x) ])
        ↓⟨ F.homomorphism ⟩
          F₁ (εY (H₀ x)) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ˡ C.identityˡ ⟩
          (C.id C.∘ F₁ (εY (H₀ x))) C.∘
            F₁ (H₁ (ηY x))
        ↓⟨ C.∘-resp-≡ˡ (C.∘-resp-≡ˡ X'.zig) ⟩
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
        ↑⟨ C.∘-resp-≡ˡ (C.∘-resp-≡ʳ (F-resp-≡ D.identityˡ)) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x))))) C.∘
            F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.∘-resp-≡ˡ (C.∘-resp-≡ʳ C.identityʳ) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x)))) C.∘ C.id) C.∘
            F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (H-resp-≡ (E.∘-resp-≡ˡ (I-resp-≡ D.identityˡ)))) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x)))) C.∘ C.id) C.∘
            F₁ (H₁ (I₁ (D.id D.∘ ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (H-resp-≡ (E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ G.identity))))) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x)))) C.∘ C.id) C.∘
            F₁ (H₁ (I₁ (G₁ C.id D.∘ ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (H-resp-≡ (E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ (G-resp-≡ F.identity)))))) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x)))) C.∘ C.id) C.∘
            F₁ (H₁ (I₁ (G₁ (F₁ D.id) D.∘ ηX (H₀ x)) E.∘ ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (H-resp-≡ (E.∘-resp-≡ˡ E.identityʳ))) ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (D.id D.∘ εY (G₀ (F₀ (H₀ x)))) C.∘ C.id) C.∘
              F₁ (H₁ ((I₁ (G₁ (F₁ D.id) D.∘ ηX (H₀ x)) E.∘ E.id) E.∘ ηY x))
        ∎
      where open C.HomReasoning -}

    .zag' : {x : C.Obj} →
              NaturalTransformation.η idT x E.≡
                NaturalTransformation.η
                (((I ∘F G) ∘ˡ (Xε' ∘₁ (F ∘ˡ (Yε' ∘ʳ G)))) ∘₁
                 (((I ∘ˡ (Xη' ∘ʳ H)) ∘₁ Yη') ∘ʳ (I ∘F G)))
                x
    zag' {x} = {!!} {-
        begin
          E.id
        ↓⟨ Y'.zag ⟩
          (I₁ (εY (G₀ x))) E.∘ (ηY (I₀ (G₀ x)))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ D.identityˡ) ⟩
          (I₁ (D.id D.∘ (εY (G₀ x)))) E.∘ (ηY (I₀ (G₀ x)))
        ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ X'.zag)) ⟩
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
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ (G-resp-≡ (C.∘-resp-≡ʳ (F-resp-≡ D.identityˡ)))) ⟩
          I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)))) E.∘
            I₁ (ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ (G-resp-≡ (C.∘-resp-≡ʳ C.identityʳ))) ⟩
          I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)) C.∘ C.id)) E.∘
            I₁ (ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ʳ (E.∘-resp-≡ˡ (I-resp-≡ D.identityˡ)) ⟩
          I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)) C.∘ C.id)) E.∘
            I₁ (D.id D.∘ ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ʳ (E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ G.identity))) ⟩
          I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)) C.∘ C.id)) E.∘
            I₁ (G₁ C.id D.∘ ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ʳ (E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ (G-resp-≡ F.identity)))) ⟩
           I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)) C.∘ C.id)) E.∘
             I₁ (G₁ (F₁ D.id) D.∘ ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x))
        ↑⟨ E.∘-resp-≡ʳ (E.∘-resp-≡ˡ E.identityʳ) ⟩
          I₁ (G₁ (εX x C.∘ F₁ (D.id D.∘ εY (G₀ x)) C.∘ C.id)) E.∘
            (I₁ (G₁ (F₁ D.id) D.∘ ηX (H₀ (I₀ (G₀ x)))) E.∘ E.id) E.∘ ηY (I₀ (G₀ x))
        ∎
      where open E.HomReasoning -}

infix  4 _≡_

_≡_ : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {F : Functor D C} {G : Functor C D} → Rel (F ⊣ G) (o ⊔ e ⊔ o₁ ⊔ e₁)
_≡_ {C = C} {D} {F} {G} X Y = Adjunction.unit X ≡T Adjunction.unit Y ×
                                Adjunction.counit X ≡T Adjunction.counit Y

.equiv : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {F : Functor D C} {G : Functor C D} → IsEquivalence (_≡_ {F = F} {G})
equiv {C = C} {D} {F} {G} = record
         { refl = (D.Equiv.refl), (C.Equiv.refl)
         ; sym = λ {T U : F ⊣ G} → sym' {T = T} {U = U}
         ; trans = λ {T U V : F ⊣ G} → trans' {T = T} {U = U} {V = V}
         }
      where
        module C = Category C
        module D = Category D

        sym' : {T U : F ⊣ G} → (H : T ≡ U) → flip _≡_ T U
        sym' {T} {U} (H₁ , H₂) = (λ {x} → D.Equiv.sym H₁) , (λ {x} → C.Equiv.sym H₂)

        trans' : {T U V : F ⊣ G} → T ≡ U → U ≡ V → T ≡ V
        trans' {T} {U} {V} (H₁ , H₂) (H₃ , H₄) = (λ {x} → D.Equiv.trans H₁ H₃) , (C.Equiv.trans H₂ H₄)

setoid : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {F : Functor D C} {G : Functor C D}
         → Setoid (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) (o ⊔ e ⊔ o₁ ⊔ e₁)
setoid {C = C} {D} {F} {G} = record
       { Carrier = Adjunction F G
       ; _≈_ = _≡_
       ; isEquivalence = equiv {F = F} {G = G}
       }

.assoc : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
           {C₀ : Category o₀ ℓ₀ e₀} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂} {C₃ : Category o₃ ℓ₃ e₃}
           {F : Functor C₀ C₁} {G : Functor C₁ C₂} {H : Functor C₂ C₃}
           {F′ : Functor C₁ C₀} {G′ : Functor C₂ C₁} {H′ : Functor C₃ C₂}
           {T : F ⊣ F′} {U : G ⊣ G′} {V : H ⊣ H′}
       → (V ∘ U) ∘ T ≡ V ∘ (U ∘ T)
assoc {C₀ = C₀} {C₁} {C₂} {C₃} {F} {G} {H} {F′} {G′} {H′} {T} {U} {V} = (λ {x} → {!!}) , (λ {x} → {!!})
  where
    module C₀ = Category C₀
    module C₁ = Category C₁
    module C₂ = Category C₂
    module C₃ = Category C₃
    module F = Functor F
    module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
    module F′ = Functor F′ renaming (F₀ to F′₀; F₁ to F′₁; F-resp-≡ to F′-resp-≡)
    module G′ = Functor G′ renaming (F₀ to G′₀; F₁ to G′₁; F-resp-≡ to G′-resp-≡)
    module H′ = Functor H′ renaming (F₀ to H′₀; F₁ to H′₁; F-resp-≡ to H′-resp-≡)
    open C₀
    open C₁
    open C₂
    open C₃
    open F
    open G
    open H
    open F′
    open G′
    open H′

.identityˡ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} {G : Functor D C} {T : F ⊣ G}
             → id ∘ T ≡ T
identityˡ {C = C} {D} {F} {G} {T} = ( (λ {x} → pf₀ {x}) , (λ {x} → pf₁ {x}) )
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

    pf₀ : {x : C.Obj} → NaturalTransformation.η (Adjunction.unit (id ∘ T)) x C.≡
                          NaturalTransformation.η (Adjunction.unit T) x
    pf₀ {x} = {!!}
      where open C.HomReasoning

    pf₁ : {x : D.Obj} → NaturalTransformation.η (Adjunction.counit (id ∘ T)) x D.≡
                          NaturalTransformation.η (Adjunction.counit T) x
    pf₁ {x} = {!!}
      where open D.HomReasoning

.identityʳ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} {G : Functor D C} {T : F ⊣ G}
             → T ∘ id ≡ T
identityʳ {C = C} {D} {F} {G} {T} = {!!}

.∘-resp-≡  : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
               {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
               {F : Functor B C} {G : Functor A B} {F′ : Functor C B} {G′ : Functor B A}
               {T T′ : G ⊣ G′} {U U′ : F ⊣ F′}
           → T ≡ T′ → U ≡ U′ → U ∘ T ≡ U′ ∘ T′
∘-resp-≡ {A = A} {B} {C} {F} {G} {F′} {G′} {T} {T′} {U} {U′} T≡T′ U≡U′ = {!!} {-helper (G≡I q) (F≡H (Functor.F₁ I q))
  where
  open Heterogeneous C
  module C = Category C
  helper : ∀ {a b c d} {z w} {f : B [ a , b ]} {h : B [ c , d ]} {i : C [ z , w ]}
         → B [ f ∼ h ] → C [ Functor.F₁ F h ∼ i ] → C [ Functor.F₁ F f ∼ i ]
  helper (≡⇒∼ f≡h) (≡⇒∼ g≡i) = ≡⇒∼ (C.Equiv.trans (Functor.F-resp-≡ F f≡h) g≡i) -}
