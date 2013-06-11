{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.IndexedProduct {o a} (C : Category o a) where

-- An indexed product is similar to a limit, but the diagram is from a Set
--  rather than a category, so there are no subobjects involved.
 
open Category C
open Equiv

open import Level
open import Relation.Binary as Bi using ()

open import Categories.Support.PropositionalEquality
open import Categories.Operations

import Categories.Object.Indexed as IObj
import Categories.Morphism.Indexed as IArrow

-- Borrowed from Dan Doel's definition of products
record IndexedProduct {c} (B : Set c) (As : IObj.Dust C B) : Set (o ⊔ a ⊔ c) where
  open Heterogeneous C
  open IObj C B
  open IArrow C B

  Cone : Obj → _
  Cone apex = apex ⇒∗ As

  _≜_ : ∀ {apex} → Bi.Rel (Cone apex) _
  _≜_ {apex} = _≣_

  field
    ∏ : Obj
    π : Cone ∏

  -- convenience!
  π[_] : (x : B) → (∏ ⇒ (As ! x))
  π[_] = π

  -- .π-cong : ∀ {x y} → x ≣ y → (π[ x ] ∼ π[ y ])
  -- π-cong = Heterogeneous.cong C

  π▹_ : ∀ {X} (f : X ⇒ ∏) → Cone X
  π▹_ f = _▹_ {Zs = As} π f 

  field
    uncurry : ∀ {V} → Cone V → V ⇒ ∏
    -- XXX fs should be implicit but call sites can't infer it
    --   because of eta-driven irrelevant-field dropping
    .commute∗ : ∀ {V} (fs : Cone V) → (π▹ uncurry fs) ≜ fs
    .universal : ∀ {V} (fs : Cone V) {i : V ⇒ ∏}
               → (∀ {x} → π[ x ] ∘ i ≡ fs x) → uncurry fs ≡ i

  -- convenience?
  .commute : ∀ {V} (fs : Cone V) {x} → (π[ x ] ∘ uncurry fs) ≡ fs x
  commute fs {x} = ≣-app (commute∗ fs) x

  .universal∗ : ∀ {V} (fs : Cone V) {i : V ⇒ ∏}
              → ((π▹ i) ≜ fs) → uncurry fs ≡ i
  universal∗ fs pf = universal fs (≣-app pf _)

  .g-η : ∀ {C} {f : C ⇒ ∏} → (uncurry (π▹ f) ≡ f)
  g-η {f = f} = universal (π▹ f) Equiv.refl

  .η : uncurry π ≡ Category.id C
  η = universal π identityʳ

  .uncurry-cong : ∀ {V} {fs gs : Cone V} → (∀ {x} → fs x ≡ gs x) → uncurry fs ≡ uncurry gs
  uncurry-cong {fs = fs} {gs} eq = 
    universal fs (Equiv.trans (commute gs) (Equiv.sym eq))

  .uncurry-cong∗ : ∀ {V} {fs gs : Cone V} → fs ≜ gs → uncurry fs ≡ uncurry gs
  uncurry-cong∗ {V} {fs} {gs} eq = universal∗ fs 
      (≣-trans (commute∗ gs) (≣-sym eq))

  .uncurry∘ : ∀ {V W} (fs : Cone V) {q : W ⇒ V} → (uncurry fs) ∘ q ≡ uncurry (_▹_ {Zs = As} fs q)
  uncurry∘ fs {q} = Equiv.sym (universal (_▹_ {Zs = As} fs q) (Equiv.trans (Equiv.sym assoc) (∘-resp-≡ˡ (commute fs))))

import Categories.Morphisms
open import Categories.Square
open Categories.Morphisms C
open GlueSquares C

module _ {c B As} where
  open IndexedProduct {c} {B} {As}
  Prod = IndexedProduct B As
  open IObj C B
  open IArrow C B
  open _≅_ using () renaming (f to fwd; g to rev)

  private
    module Lemmas where

      repack : (p₁ p₂ : Prod) → ∏ p₁ ⇒ ∏ p₂
      repack p₁ p₂ = uncurry p₂ (π p₁)

      .repack∘ : (p₁ p₂ p₃ : Prod) → repack p₂ p₃ ∘ repack p₁ p₂ ≡ repack p₁ p₃
      repack∘ p₁ p₂ p₃ = sym (universal p₃ _
        (glueTrianglesʳ (commute p₃ _) (commute p₂ _)))

      .repack≡id : (p : Prod) → repack p p ≡ id
      repack≡id p = η p

      .repack-cancel : (p₁ p₂ : Prod) → repack p₁ p₂ ∘ repack p₂ p₁ ≡ id
      repack-cancel p₁ p₂ = trans (repack∘ p₂ p₁ p₂) (repack≡id p₂)

  up-to-iso : ∀ (p₁ p₂ : Prod) → ∏ p₁ ≅ ∏ p₂
  up-to-iso p₁ p₂ = record
    { f = repack p₁ p₂
    ; g = repack p₂ p₁
    ; iso = record
      { isoˡ = repack-cancel p₂ p₁
      ; isoʳ = repack-cancel p₁ p₂
      }
    }
    where
    open Lemmas

  .up-to-iso-ok : ∀ (p₁ p₂ : Prod) → π p₁ ▹ rev (up-to-iso p₁ p₂) ≣ π p₂
  up-to-iso-ok p₁ p₂ = commute∗ p₁ (π p₂)

  .up-to-iso-unique : (p₁ p₂ : Prod) (i : ∏ p₁ ≅ ∏ p₂) (eq : π p₁ ▹ rev i ≣ π p₂)
                   → up-to-iso p₁ p₂ ≣ i
  up-to-iso-unique p₁ p₂ i eq = promote (up-to-iso p₁ p₂) i (record
    { f-≡ = universal p₂ (π p₁) (≣-sym (switch-gfʳ i (≣-app eq _)))
    ; g-≡ = universal∗ p₁ (π p₂) eq
    })
    where
    open EasyCategory Coreᵉ using (promote)

  .iso-unique : (p₁ p₂ : Prod) (i j : ∏ p₁ ≅ ∏ p₂)
                (eq-i : π p₁ ▹ _≅_.g i ≣ π p₂) (eq-j : π p₁ ▹ _≅_.g j ≣ π p₂)
              → i ≣ j
  iso-unique p₁ p₂ i j eq-i eq-j = ≣-trans (≣-sym (up-to-iso-unique p₁ p₂ i eq-i))
                                           (       up-to-iso-unique p₁ p₂ j eq-j )

  transport-by-iso : (p : Prod) → ∀ {X} → ∏ p ≅ X → Prod
  transport-by-iso p {X} p≅X = record
    { ∏ = X
    ; π = p.π ▹ g
    ; uncurry = λ fs → f ∘ p.uncurry fs
    ; commute∗ = λ fs → ≣-ext λ b → trans (cancelInner isoˡ) (p.commute fs)
    ; universal = λ fs {i} pfs → let open HomReasoning in
        begin
          f ∘ p.uncurry fs
        ↑⟨ ∘-resp-≡ʳ (p.uncurry-cong pfs) ⟩
          f ∘ p.uncurry ((p.π ▹ g) ▹ i)
        ↓⟨ ∘-resp-≡ʳ (p.universal _ (sym assoc)) ⟩
          f ∘ (g ∘ i)
        ↓⟨ cancelLeft isoʳ ⟩
          i
        ∎
    }
    where
    module p = IndexedProduct p
    open _≅_ p≅X

  .iso-classify : (p : Prod) → ∀ {X} {i j : ∏ p ≅ X} → π p ▹ rev i ≣ π p ▹ rev j
                → i ≣ j
  iso-classify p {i = i} {j} eq = iso-unique p (transport-by-iso p j) i j eq ≣-refl

  -- more general
  .jointly-monic : (p : Prod) → ∀ {X} {f g : X ⇒ ∏ p} → π p ▹ f ≣ π p ▹ g → f ≣ g
  jointly-monic p {f = f} {g} eq = ≣-trans (≣-sym (universal∗ p _ eq)) (g-η p)
{-
Reversible : ∀ {A B} → (p : Product A B) → Product B A
Reversible p = record
  { A×B = p.A×B
  ; π₁ = p.π₂
  ; π₂ = p.π₁
  ; ⟨_,_⟩ = flip p.⟨_,_⟩
  ; commute₁ = p.commute₂
  ; commute₂ = p.commute₁
  ; universal = flip p.universal
  }
  where module p = Product p

Commutative : ∀ {A B} (p₁ : Product A B) (p₂ : Product B A) → Product.A×B p₁ ≅ Product.A×B p₂
Commutative p₁ p₂ = up-to-iso p₁ (Reversible p₂)

Associable : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) → Product (Product.A×B p₁) Z
Associable p₁ p₂ p₃ = record
  { A×B = A×B p₃
  ; π₁ = p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩
  ; π₂ = π₂ p₂ ∘ π₂ p₃
  ; ⟨_,_⟩ = λ f g → p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
  ; commute₁ = λ {_ f g} → let open HomReasoning in begin
      p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
    ↓⟨ ⟨⟩∘ p₁ ⟩
      p₁ ⟨ π₁ p₃ ∘ p₃ ⟨ π₁ p₁ ∘ f , _ ⟩ , (π₁ p₂ ∘ π₂ p₃) ∘ p₃ ⟨ _ , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₁ (commute₁ p₃) (glueTrianglesˡ (commute₁ p₂) (commute₂ p₃)) ⟩
      p₁ ⟨ π₁ p₁ ∘ f , π₂ p₁ ∘ f ⟩
    ↓⟨ g-η p₁ ⟩
      f
    ∎
  ; commute₂ = λ {_ f g} → glueTrianglesˡ (commute₂ p₂) (commute₂ p₃)
  ; universal = λ {D l r i} pfˡ pfʳ → let open HomReasoning in begin
      p₃ ⟨ π₁ p₁ ∘ l , p₂ ⟨ π₂ p₁ ∘ l , r ⟩ ⟩
    ↑⟨ ⟨⟩-cong₂ p₃ (∘-resp-≡ʳ pfˡ) (⟨⟩-cong₂ p₂ (∘-resp-≡ʳ pfˡ) pfʳ) ⟩
      p₃ ⟨ π₁ p₁ ∘ (p₁ ⟨ π₁ p₃ , _ ⟩ ∘ i) , p₂ ⟨ π₂ p₁ ∘ (p₁ ⟨ _ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i) , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₃ (pullˡ (commute₁ p₁)) (⟨⟩-cong₂ p₂ (pullˡ (commute₂ p₁)) refl) ⟩
      p₃ ⟨ π₁ p₃ ∘ i , p₂ ⟨ (π₁ p₂ ∘ π₂ p₃) ∘ i , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩
    ↓⟨ ⟨⟩-cong₂ p₃ refl (universal p₂ (sym assoc) (sym assoc)) ⟩
      p₃ ⟨ π₁ p₃ ∘ i , π₂ p₃ ∘ i ⟩
    ↓⟨ g-η p₃ ⟩
      i
    ∎
  }
  where
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)

Associative : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) → (Product.A×B p₃) ≅ (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = up-to-iso (Associable p₁ p₂ p₃) p₄

open Lemmas public

Mobile : ∀ {A₁ B₁ A₂ B₂} (p : Product A₁ B₁) → A₁ ≅ A₂ → B₁ ≅ B₂ → Product A₂ B₂
Mobile p A₁≅A₂ B₁≅B₂ = record
  { A×B = p.A×B
  ; π₁ = f A₁≅A₂ ∘ p.π₁
  ; π₂ = f B₁≅B₂ ∘ p.π₂
  ; ⟨_,_⟩ = λ h k → p ⟨ g A₁≅A₂ ∘ h , g B₁≅B₂ ∘ k ⟩
  ; commute₁ = let open HomReasoning in begin
      (f A₁≅A₂ ∘ p.π₁) ∘ p ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩
    ↓⟨ pullʳ p.commute₁ ⟩
      f A₁≅A₂ ∘ (g A₁≅A₂ ∘ _)
    ↓⟨ cancelLeft (isoʳ A₁≅A₂) ⟩
      _
    ∎
  ; commute₂ = let open HomReasoning in begin
      (f B₁≅B₂ ∘ p.π₂) ∘ p ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩
    ↓⟨ pullʳ p.commute₂ ⟩
      f B₁≅B₂ ∘ (g B₁≅B₂ ∘ _)
    ↓⟨ cancelLeft (isoʳ B₁≅B₂) ⟩
      _
    ∎
  ; universal = λ pfˡ pfʳ → p.universal 
                              (switch-fgˡ A₁≅A₂ (trans (sym assoc) pfˡ))
                              (switch-fgˡ B₁≅B₂ (trans (sym assoc) pfʳ))
  }
  where
  module p = Product p
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)
  open _≅_
-}
