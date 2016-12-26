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
open import Categories.Comonad
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

  comonad : Comonad C
  comonad = record
    { F = F ∘F G
    ; ε = counit
    ; δ = F ∘ˡ (unit ∘ʳ G)
    ; assoc = assoc′
    ; identityˡ = identityˡ′
    ; identityʳ = identityʳ′
    }
    where
      open C.HomReasoning
      .assoc′ : ∀ {x} → F₁ (unit.η (G₀ (F₀ (G₀ x)))) C.∘ F₁ (unit.η (G₀ x)) C.≡ F₁ (G₁ (F₁ (unit.η (G₀ x)))) C.∘ F₁ (unit.η (G₀ x))
      assoc′ {x} =
        begin
          F₁ (unit.η (G₀ (F₀ (G₀ x)))) C.∘ F₁ (unit.η (G₀ x))
        ↑⟨ F.homomorphism ⟩
          F₁ (unit.η (G₀ (F₀ (G₀ x))) D.∘ unit.η (G₀ x))
        ↓⟨ F-resp-≡ (NaturalTransformation.commute unit (unit.η (G₀ x))) ⟩
          F₁ (G₁ (F₁ (unit.η (G₀ x))) D.∘ unit.η (G₀ x))
        ↓⟨ F.homomorphism ⟩
          F₁ (G₁ (F₁ (unit.η (G₀ x)))) C.∘ F₁ (unit.η (G₀ x))
        ∎

      .identityˡ′ : ∀ {x} → (F₁ (G₁ (counit.η x))) C.∘ F₁ (unit.η (G₀ x)) C.≡ C.id
      identityˡ′ {x} =
        begin
          (F₁ (G₁ (counit.η x))) C.∘ F₁ (unit.η (G₀ x))
        ↑⟨ F.homomorphism ⟩
          F₁ (G₁ (counit.η x) D.∘ unit.η (G₀ x))
        ↓⟨ F-resp-≡ (D.Equiv.sym zag) ⟩
          F₁ D.id
        ↓⟨ F.identity ⟩
          C.id
        ∎

      .identityʳ′ : ∀ {x} → counit.η (F₀ (G₀ x)) C.∘ F₁ (unit.η (G₀ x)) C.≡ C.id
      identityʳ′ {x} = C.Equiv.sym zig

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

infix  4 _≡_

_≡_ : ∀ {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} {F : Functor D C} {G : Functor C D} →  Rel (F ⊣ G) (o ⊔ e ⊔ o₁ ⊔ e₁)
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
