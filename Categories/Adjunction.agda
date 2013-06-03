{-# OPTIONS --universe-polymorphism #-}
module Categories.Adjunction where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalTransformation renaming (id to idT)
open import Categories.Monad
open import Categories.Square

record Adjunction {o a} {o₁ a₁} {C : Category o a} {D : Category o₁ a₁} (F : Functor D C) (G : Functor C D) : Set (o ⊔ a ⊔ o₁ ⊔ a₁) where
  field
    unit   : NaturalTransformation idF (G ∘F F)
    counit : NaturalTransformation (F ∘F G) idF

    .zig : idT ≡ (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : idT ≡ (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

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

id : ∀ {o a} {C : Category o a} → Adjunction (idF {C = C}) (idF {C = C})
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
_∘_ : ∀ {o a} {o₁ a₁} {o₂ a₂} {C : Category o a} {D : Category o₁ a₁} {E : Category o₂ a₂}
      {F : Functor D C} {G : Functor C D} {H : Functor E D} {I : Functor D E} →
      Adjunction F G → Adjunction H I → Adjunction (F ∘F H) (I ∘F G)
_∘_ {C = C} {D} {E} {F} {G} {H} {I} X Y = record
  { unit = (I ∘ˡ (Xη ∘ʳ H)) ∘₁ Yη
  ; counit = Xε ∘₁ (F ∘ˡ (Yε ∘ʳ G))
  ; zig = zig'
  ; zag = zag'
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
    module I = Functor I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)
    private module X = Adjunction X renaming (unit to Xη; counit to Xε)
    private module Y = Adjunction Y renaming (unit to Yη; counit to Yε)
    private module Xη = NaturalTransformation X.Xη renaming (η to ηX)
    private module Yη = NaturalTransformation Y.Yη renaming (η to ηY)
    private module Xε = NaturalTransformation X.Xε renaming (η to εX)
    private module Yε = NaturalTransformation Y.Yε renaming (η to εY)
    open F
    open G
    open H
    open I
    open X
    open Y
    open Xη
    open Yη
    open Xε
    open Yε

    .zig' : {x : E.Obj} →
              C.id C.≡
                (εX (F₀ (H₀ x)) C.∘ F₁ (εY (G₀ (F₀ (H₀ x))))) C.∘
                F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
    zig' {x} =
        begin
          C.id
        ↑⟨ F.identity ⟩
          F₁ D.id
        ↓⟨ F-resp-≡ Y.zig ⟩
          F₁ (D [ εY (H₀ x) ∘ H₁ (ηY x) ])
        ↓⟨ F.homomorphism ⟩
          F₁ (εY (H₀ x)) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ pullˡ (cancelLeft (C.Equiv.sym X.zig)) ⟩
          εX (F₀ (H₀ x)) C.∘ (F₁ (ηX (H₀ x)) C.∘ F₁ (εY (H₀ x))) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ (C.∘-resp-≡ˡ F.homomorphism) ⟩
          εX (F₀ (H₀ x)) C.∘ F₁ (ηX (H₀ x) D.∘ εY (H₀ x)) C.∘ F₁ (H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ F.homomorphism ⟩
          εX (F₀ (H₀ x)) C.∘ F₁ ((ηX (H₀ x) D.∘ εY (H₀ x)) D.∘ H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (D.∘-resp-≡ˡ (Yε.commute (ηX (H₀ x))))) ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ ((εY (G₀ (F₀ (H₀ x))) D.∘ H₁ (I₁ (ηX (H₀ x)))) D.∘ H₁ (ηY x))
        ↑⟨ C.∘-resp-≡ʳ (F-resp-≡ (GlueSquares.pushʳ D H.homomorphism)) ⟩
          εX (F₀ (H₀ x)) C.∘
            F₁ (D [ εY (G₀ (F₀ (H₀ x))) ∘ H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x) ])
        ↓⟨ pushʳ F.homomorphism ⟩
          (εX (F₀ (H₀ x)) C.∘ F₁ (εY (G₀ (F₀ (H₀ x))))) C.∘
            F₁ (H₁ (I₁ (ηX (H₀ x)) E.∘ ηY x))
        ∎
      where
      open C.HomReasoning
      open GlueSquares C

    .zag' : {x : C.Obj} →
              E.id E.≡
              I₁ (G₁ (εX x C.∘ F₁ (εY (G₀ x)))) E.∘
              (I₁ (ηX (H₀ (I₀ (G₀ x)))) E.∘ ηY (I₀ (G₀ x)))
    zag' {x} =
        begin
          E.id
        ↓⟨ Y.zag ⟩
          (I₁ (εY (G₀ x))) E.∘ (ηY (I₀ (G₀ x)))
        ↑⟨ E.∘-resp-≡ˡ (I-resp-≡ D.identityˡ) ⟩
          (I₁ (D.id D.∘ (εY (G₀ x)))) E.∘ (ηY (I₀ (G₀ x)))
        ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ (D.∘-resp-≡ˡ X.zag)) ⟩
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
