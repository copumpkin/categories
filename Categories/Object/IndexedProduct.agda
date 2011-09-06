{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.IndexedProduct {o ℓ e} (C : Category o ℓ e) where

-- An indexed product is similar to a limit, but the diagram is from a Set
--  (irrelevant Setoid here) rather than a category, so there are no subobjects
--  involved.
 
open Category C
open Equiv

open import Level
open import Relation.Binary as Bi using ()
open import Categories.Support.Equivalence
import Categories.Object.Indexed as IObj
import Categories.Morphism.Indexed as IArrow

-- Borrowed from Dan Doel's definition of products
record IndexedProduct {c q} (B : Setoid c q) (As : IObj.Dust C B) : Set (o ⊔ ℓ ⊔ e ⊔ c ⊔ q) where
  module B = Setoid B
  open B using (_≈_)
  open Heterogeneous C
  open IObj C B
  open IArrow C B

  Cone : Obj → _
  Cone apex = apex ⇒∗ As

  cone-setoid : Obj → Setoid _ _
  cone-setoid apex = fan-setoid apex As

  _≜_ : ∀ {apex} → Bi.Rel (Cone apex) _
  _≜_ {apex} = Setoid._≈_ (cone-setoid apex)

  field
    ∏ : Obj
    π : Cone ∏

  -- convenience!
  π[_] : (x : B.Carrier) → (∏ ⇒ (As ! x))
  π[_] x = π ‼ x
  -- ↑ XXX for some reason it won't parse as π[ x ]
  .π-cong : ∀ {x y} → x ≈ y → (π[ x ] ∼ π[ y ])
  π-cong x≈y = cong₁ π x≈y

  π▹_ : ∀ {X} (f : X ⇒ ∏) → Cone X
  π▹_ f = _▹_ {Zs = As} π f 

  field
    uncurry : ∀ {V} → Cone V → V ⇒ ∏
    -- XXX fs should be implicit but call sites can't infer it
    --   because of eta-driven irrelevant-field dropping
    .commute∗ : ∀ {V} (fs : Cone V) → (π▹ uncurry fs) ≜ fs
    .universal : ∀ {V} (fs : Cone V) {i : V ⇒ ∏}
               → (∀ {x} → π[ x ] ∘ i ≡ fs ‼ x) → uncurry fs ≡ i

  -- convenience?
  .commute : ∀ {V} (fs : Cone V) {x} → (π[ x ] ∘ uncurry fs) ≡ fs ‼ x
  commute fs {x} = ∼⇒≡ (commute∗ fs B.refl)

  .universal∗ : ∀ {V} (fs : Cone V) {i : V ⇒ ∏}
              → ((π▹ i) ≜ fs) → uncurry fs ≡ i
  universal∗ fs pf = universal fs (∼⇒≡ (pf B.refl))

  .g-η : ∀ {C} {f : C ⇒ ∏} → (uncurry (π▹ f) ≡ f)
  g-η {f = f} = universal (π▹ f) Equiv.refl

  .η : uncurry π ≡ Category.id C
  η = universal π identityʳ

  .uncurry-cong : ∀ {V} {fs gs : Cone V} → (∀ {x} → fs ‼ x ≡ gs ‼ x) → uncurry fs ≡ uncurry gs
  uncurry-cong {fs = fs} {gs} eq = 
    universal fs (Equiv.trans (commute gs) (Equiv.sym eq))

  .uncurry-cong∗ : ∀ {V} {fs gs : Cone V} → fs ≜ gs → uncurry fs ≡ uncurry gs
  uncurry-cong∗ {V} {fs} {gs} eq = universal∗ fs 
      (≜-trans {π▹ uncurry gs} {gs} {fs} (commute∗ gs) (≜-sym {fs} {gs} eq))
    where
    open Setoid (cone-setoid V) using ()
                                renaming (trans to ≜-trans; sym to ≜-sym)


  .uncurry∘ : ∀ {V W} (fs : Cone V) {q : W ⇒ V} → (uncurry fs) ∘ q ≡ uncurry (_▹_ {Zs = As} fs q)
  uncurry∘ fs {q} = Equiv.sym (universal (_▹_ {Zs = As} fs q) (Equiv.trans (Equiv.sym assoc) (∘-resp-≡ˡ (commute fs))))

{-
open import Categories.Morphisms

Commutative : ∀ {A B} → (p₁ : Product A B) (p₂ : Product B A) → _≅_ C (Product.A×B p₁) (Product.A×B p₂)
Commutative p₁ p₂ = record 
  { f = ⟨ π₂ , π₁ ⟩′
  ; g = ⟨ π′₂ , π′₁ ⟩
  ; iso = record 
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where
  module p₁ = Product p₁
  module p₂ = Product p₂
  open Product p₁
  open Product p₂ renaming (A×B to B×A; π₁ to π′₁; π₂ to π′₂; ⟨_,_⟩ to ⟨_,_⟩′)

  idˡ : A×B ⇒ A×B
  idˡ = ⟨ π′₂ , π′₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩′

  idʳ : B×A ⇒ B×A
  idʳ = ⟨ π₂ , π₁ ⟩′ ∘ ⟨ π′₂ , π′₁ ⟩

  .idˡ-commutes₁ : π₁ ∘ idˡ ≡ π₁
  idˡ-commutes₁ = begin
                    π₁ ∘ idˡ
                  ↑⟨ assoc ⟩ 
                    (π₁ ∘ ⟨ π′₂ , π′₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩′
                  ↓⟨ ∘-resp-≡ˡ p₁.commute₁ ⟩
                    π′₂ ∘ ⟨ π₂ , π₁ ⟩′
                  ↓⟨ p₂.commute₂ ⟩
                    π₁
                  ∎
    where 
    open HomReasoning

  .idˡ-commutes₂ : π₂ ∘ idˡ ≡ π₂
  idˡ-commutes₂ = begin
                    π₂ ∘ idˡ
                  ↑⟨ assoc ⟩ 
                    (π₂ ∘ ⟨ π′₂ , π′₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩′
                  ↓⟨ ∘-resp-≡ˡ p₁.commute₂ ⟩
                    π′₁ ∘ ⟨ π₂ , π₁ ⟩′
                  ↓⟨ p₂.commute₁ ⟩
                    π₂
                  ∎
    where 
    open HomReasoning

  .isoˡ : idˡ ≡ id
  isoˡ = begin
           idˡ
         ↑⟨ p₁.universal idˡ-commutes₁ idˡ-commutes₂ ⟩
           ⟨ π₁ , π₂ ⟩
         ↓⟨ p₁.η ⟩
           id
         ∎
    where 
    open HomReasoning


  .idʳ-commutes₁ : π′₁ ∘ idʳ ≡ π′₁
  idʳ-commutes₁ = begin
                    π′₁ ∘ idʳ
                  ↑⟨ assoc ⟩ 
                    (π′₁ ∘ ⟨ π₂ , π₁ ⟩′) ∘ ⟨ π′₂ , π′₁ ⟩
                  ↓⟨ ∘-resp-≡ˡ p₂.commute₁ ⟩
                    π₂ ∘ ⟨ π′₂ , π′₁ ⟩
                  ↓⟨ p₁.commute₂ ⟩
                    π′₁
                  ∎
    where 
    open HomReasoning

  .idʳ-commutes₂ : π′₂ ∘ idʳ ≡ π′₂
  idʳ-commutes₂ = begin
                    π′₂ ∘ idʳ
                  ↑⟨ assoc ⟩ 
                    (π′₂ ∘ ⟨ π₂ , π₁ ⟩′) ∘ ⟨ π′₂ , π′₁ ⟩
                  ↓⟨ ∘-resp-≡ˡ p₂.commute₂ ⟩
                    π₁ ∘ ⟨ π′₂ , π′₁ ⟩
                  ↓⟨ p₁.commute₁ ⟩
                    π′₂
                  ∎
    where 
    open HomReasoning

  .isoʳ : idʳ ≡ id
  isoʳ = begin
           idʳ
         ↑⟨ p₂.universal idʳ-commutes₁ idʳ-commutes₂ ⟩
           ⟨ π′₁ , π′₂ ⟩′
         ↓⟨ p₂.η ⟩
           id
         ∎
    where 
    open HomReasoning


Associative : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) → _≅_ C (Product.A×B p₃) (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = record 
  { f = f
  ; g = g
  ; iso = record 
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where
  module p₁ = Product p₁
  module p₂ = Product p₂
  module p₃ = Product p₃
  module p₄ = Product p₄
  open Product p₁ hiding (π₁; π₂) renaming (⟨_,_⟩ to ⟨_,_⟩p₁)
  open Product p₂ hiding (π₁; π₂) renaming (A×B to B×C; ⟨_,_⟩ to ⟨_,_⟩p₂)
  open Product p₃ renaming (A×B to A×[B×C])
  open Product p₄ renaming (A×B to [A×B]×C; π₁ to π′₁; π₂ to π′₂; ⟨_,_⟩ to ⟨_,_⟩′)
  
  f : A×[B×C] ⇒ [A×B]×C
  f = ⟨ ⟨ π₁ , p₂.π₁ ∘ π₂ ⟩p₁ , p₂.π₂ ∘ π₂ ⟩′

  g : [A×B]×C ⇒ A×[B×C]
  g = ⟨ p₁.π₁ ∘ π′₁ , ⟨ p₁.π₂ ∘ π′₁ , π′₂ ⟩p₂ ⟩
  
  idˡ : A×[B×C] ⇒ A×[B×C]
  idˡ = g ∘ f

  idʳ : [A×B]×C ⇒ [A×B]×C
  idʳ = f ∘ g

  .cmˡ₁ : π₁ ∘ idˡ ≡ π₁
  cmˡ₁ = begin 
           π₁ ∘ idˡ
         ↑⟨ assoc ⟩
           (π₁ ∘ g) ∘ f
         ↓⟨ ∘-resp-≡ˡ p₃.commute₁ ⟩
           (p₁.π₁ ∘ π′₁) ∘ f
         ↓⟨ assoc ⟩
           p₁.π₁ ∘ (π′₁ ∘ f)
         ↓⟨ ∘-resp-≡ʳ p₄.commute₁ ⟩
           p₁.π₁ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁
         ↓⟨ p₁.commute₁ ⟩
           p₃.π₁
         ∎
    where
    open HomReasoning

  .cmˡ₂₁ : p₂.π₁ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f) ≡ p₂.π₁ ∘ p₃.π₂
  cmˡ₂₁ = begin
           p₂.π₁ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f)
         ↑⟨ assoc ⟩
           (p₂.π₁ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂) ∘ f
         ↓⟨ ∘-resp-≡ˡ p₂.commute₁ ⟩
           (p₁.π₂ ∘ p₄.π₁) ∘ f
         ↓⟨ assoc ⟩
           p₁.π₂ ∘ (p₄.π₁ ∘ f)
         ↓⟨ ∘-resp-≡ʳ p₄.commute₁ ⟩
           p₁.π₂ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁
         ↓⟨ p₁.commute₂ ⟩
           p₂.π₁ ∘ p₃.π₂
         ∎
    where
      open HomReasoning

  .cmˡ₂₂ : p₂.π₂ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f) ≡ p₂.π₂ ∘ p₃.π₂
  cmˡ₂₂ = begin
           p₂.π₂ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f)
         ↑⟨ assoc ⟩
           (p₂.π₂ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂) ∘ f
         ↓⟨ ∘-resp-≡ˡ p₂.commute₂ ⟩
           p₄.π₂ ∘ f
         ↓⟨ p₄.commute₂ ⟩
           p₂.π₂ ∘ p₃.π₂
         ∎
    where
      open HomReasoning

  .cmˡ₂ : π₂ ∘ idˡ ≡ π₂
  cmˡ₂ = begin
           π₂ ∘ idˡ
         ↑⟨ assoc ⟩
           (π₂ ∘ g) ∘ f
         ↓⟨ ∘-resp-≡ˡ p₃.commute₂ ⟩
           ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f
         ↑⟨ p₂.universal cmˡ₂₁ cmˡ₂₂ ⟩
           ⟨ p₂.π₁ ∘ p₃.π₂ , p₂.π₂ ∘ p₃.π₂ ⟩p₂
         ↓⟨ p₂.g-η ⟩
           p₃.π₂
         ∎
    where
    open HomReasoning

  .isoˡ : idˡ ≡ id
  isoˡ = begin
           idˡ
         ↑⟨ p₃.universal cmˡ₁ cmˡ₂ ⟩
           ⟨ π₁ , π₂ ⟩
         ↓⟨ p₃.η ⟩
           id
         ∎
    where
    open HomReasoning

  .cmʳ₁₁ : p₁.π₁ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g) ≡ p₁.π₁ ∘ p₄.π₁
  cmʳ₁₁ = begin
            p₁.π₁ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g)
          ↑⟨ assoc ⟩
            (p₁.π₁ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁) ∘ g
          ↓⟨ ∘-resp-≡ˡ p₁.commute₁ ⟩
            p₃.π₁ ∘ g
          ↓⟨ p₃.commute₁ ⟩
            p₁.π₁ ∘ p₄.π₁
          ∎
    where 
    open HomReasoning

  .cmʳ₁₂ : p₁.π₂ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g) ≡ p₁.π₂ ∘ p₄.π₁
  cmʳ₁₂ = begin
            p₁.π₂ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g)
          ↑⟨ assoc ⟩
            (p₁.π₂ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁) ∘ g
          ↓⟨ ∘-resp-≡ˡ p₁.commute₂ ⟩
            (p₂.π₁ ∘ p₃.π₂) ∘ g
          ↓⟨ assoc ⟩
            p₂.π₁ ∘ (p₃.π₂ ∘ g)
          ↓⟨ ∘-resp-≡ʳ p₃.commute₂ ⟩
            p₂.π₁ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂
          ↓⟨ p₂.commute₁ ⟩
            p₁.π₂ ∘ p₄.π₁
          ∎
    where 
    open HomReasoning


  .cmʳ₁ : π′₁ ∘ idʳ ≡ π′₁
  cmʳ₁ = begin
           π′₁ ∘ idʳ
         ↑⟨ assoc ⟩
           (π′₁ ∘ f) ∘ g
         ↓⟨ ∘-resp-≡ˡ p₄.commute₁ ⟩
           ⟨ π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g
         ↑⟨ p₁.universal cmʳ₁₁ cmʳ₁₂ ⟩
           ⟨ p₁.π₁ ∘ p₄.π₁ , p₁.π₂ ∘ p₄.π₁ ⟩p₁
         ↓⟨ p₁.g-η ⟩
           π′₁
         ∎
    where 
    open HomReasoning

  .cmʳ₂ : π′₂ ∘ idʳ ≡ π′₂
  cmʳ₂ = begin
           π′₂ ∘ idʳ
         ↑⟨ assoc ⟩
           (π′₂ ∘ f) ∘ g
         ↓⟨ ∘-resp-≡ˡ p₄.commute₂ ⟩
           (p₂.π₂ ∘ p₃.π₂) ∘ g
         ↓⟨ assoc ⟩
           p₂.π₂ ∘ (p₃.π₂ ∘ g)
         ↓⟨ ∘-resp-≡ʳ p₃.commute₂ ⟩
           p₂.π₂ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂
         ↓⟨ p₂.commute₂ ⟩
           p₄.π₂
         ∎
    where 
    open HomReasoning
    
  .isoʳ : idʳ ≡ id
  isoʳ = begin
           idʳ
         ↑⟨ p₄.universal cmʳ₁ cmʳ₂ ⟩
           ⟨ π′₁ , π′₂ ⟩′
         ↓⟨ p₄.η ⟩
           id
         ∎
    where
    open HomReasoning
-}