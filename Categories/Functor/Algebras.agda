{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Algebras where

open import Level hiding (lift)

open import Categories.Category
open import Categories.Functor hiding (_≡_; id; _∘_; equiv; assoc; identityˡ; identityʳ; ∘-resp-≡)
open import Categories.Functor.Algebra

record F-Algebra-Morphism {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} (X Y : F-Algebra F) : Set (ℓ ⊔ e) where
  constructor _,_
  open Category C
  module X = F-Algebra X
  module Y = F-Algebra Y
  open Functor F
  field
    f : X.A ⇒ Y.A
    .commutes : f ∘ X.α ≡ Y.α ∘ F₁ f

F-Algebras : ∀ {o ℓ e} {C : Category o ℓ e} → Endofunctor C → Category (ℓ ⊔ o) (e ⊔ ℓ) e
F-Algebras {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  open Category C
  open Equiv
  open Functor F

  Obj′ = F-Algebra F

  Hom′ : (A B : Obj′) → Set _
  Hom′ = F-Algebra-Morphism

  _≡′_ : ∀ {A B} (f g : Hom′ A B) → Set _
  (f , _) ≡′ (g , _) = f ≡ g

  _∘′_ : ∀ {A B C} → Hom′ B C → Hom′ A B → Hom′ A C
  _∘′_ {A} {B} {C} (f , pf₁) (g , pf₂) = _,_ {X = A} {C} (f ∘ g) pf -- TODO: find out why the hell I need to provide these implicits
    where
    module A = F-Algebra A
    module B = F-Algebra B
    module C = F-Algebra C

    .pf : (f ∘ g) ∘ A.α ≡ C.α ∘ (F₁ (f ∘ g))
    pf = begin
           (f ∘ g) ∘ A.α
         ↓⟨ assoc ⟩
           f ∘ (g ∘ A.α)
         ↓⟨ ∘-resp-≡ʳ pf₂ ⟩
           f ∘ (B.α ∘ F₁ g)
         ↑⟨ assoc ⟩
           (f ∘ B.α) ∘ F₁ g
         ↓⟨ ∘-resp-≡ˡ pf₁ ⟩
           (C.α ∘ F₁ f) ∘ F₁ g
         ↓⟨ assoc ⟩
           C.α ∘ (F₁ f ∘ F₁ g)
         ↑⟨ ∘-resp-≡ʳ homomorphism ⟩
           C.α ∘ (F₁ (f ∘ g))
         ∎
      where
      open HomReasoning

  id′ : ∀ {A} → Hom′ A A
  id′ {A} = _,_ {X = A} {A} id pf
    where
    module A = F-Algebra A

    .pf : id ∘ A.α ≡ A.α ∘ F₁ id
    pf = begin
           id ∘ A.α
         ↓⟨ identityˡ ⟩
           A.α
         ↑⟨ identityʳ ⟩
           A.α ∘ id
         ↑⟨ ∘-resp-≡ʳ identity ⟩
           A.α ∘ F₁ id
         ∎
      where
      open HomReasoning


open import Categories.Object.Initial

module Lambek {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} (I : Initial (F-Algebras F)) where
  open Category C
  open Equiv
  module FA = Category (F-Algebras F) renaming (_∘_ to _∘FA_; _≡_ to _≡FA_)
  open Functor F
  import Categories.Morphisms as Morphisms
  open Morphisms C
  open Initial I
  open F-Algebra ⊥

  lambek : A ≅ F₀ A
  lambek = record 
    { f = f′
    ; g = g′
    ; iso = iso′
    }
    where
    f′ : A ⇒ F₀ A
    f′ = F-Algebra-Morphism.f (! {lift ⊥}) 

    g′ : F₀ A ⇒ A
    g′ = α

    .iso′ : Iso f′ g′
    iso′ = record 
      { isoˡ = isoˡ′
      ; isoʳ = begin
                 f′ ∘ g′
               ↓⟨ F-Algebra-Morphism.commutes (! {lift ⊥}) ⟩
                 F₁ g′ ∘ F₁ f′
               ↑⟨ homomorphism ⟩
                 F₁ (g′ ∘ f′)
               ↓⟨ F-resp-≡ isoˡ′ ⟩
                 F₁ id
               ↓⟨ identity ⟩
                 id
               ∎
      }
      where
      open FA hiding (id; module HomReasoning)
      open HomReasoning

      isoˡ′ = ⊥-id ((_,_ {C = C} {F} g′ refl) ∘FA !)

open Lambek public
