{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Product {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A×B : Obj
    π₁ : A×B ⇒ A
    π₂ : A×B ⇒ B
    ⟨_,_⟩ : ∀ {C} → (C ⇒ A) → (C ⇒ B) → (C ⇒ A×B)

    .commute₁ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
    .commute₂ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
    .universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ A×B}
               → π₁ ∘ i ≡ f → π₂ ∘ i ≡ g → ⟨ f , g ⟩ ≡ i

  .g-η : ∀ {C} {f : C ⇒ A×B} → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f
  g-η = universal refl refl

  .η : ⟨ π₁ , π₂ ⟩ ≡ id
  η = universal identityʳ identityʳ

  .⟨⟩-cong₂ : ∀ {C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≡f′ g≡g′ = 
    universal (trans commute₁ (sym f≡f′)) (trans commute₂ (sym g≡g′))
    

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
