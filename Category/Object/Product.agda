{-# OPTIONS --universe-polymorphism #-}
open import Category

module Category.Object.Product {o ℓ e} (C : Category o ℓ e) where

open import Support hiding (_×_)
open Category.Category C

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A×B : Obj
    π₁ : Hom A×B A
    π₂ : Hom A×B B
    ⟨_,_⟩ : ∀ {C} → Hom C A → Hom C B → Hom C A×B

    .commute₁ : ∀ {C} {f : Hom C A} {g : Hom C B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
    .commute₂ : ∀ {C} {f : Hom C A} {g : Hom C B} → π₂ ∘ ⟨ f , g ⟩ ≡ g
    .universal : ∀ {C} {f : Hom C A} {g : Hom C B} {i : Hom C A×B}
               → π₁ ∘ i ≡ f
               → π₂ ∘ i ≡ g
               → ⟨ f , g ⟩ ≡ i

  .g-η : ∀ {C} {f : Hom C A×B} → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f
  g-η = universal (IsEquivalence.refl equiv) (IsEquivalence.refl equiv)

  .η : ⟨ π₁ , π₂ ⟩ ≡ id
  η = universal identityʳ identityʳ

open import Category.Morphisms


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

  idˡ : Hom A×B A×B
  idˡ = ⟨ π′₂ , π′₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩′

  idʳ : Hom B×A B×A
  idʳ = ⟨ π₂ , π₁ ⟩′ ∘ ⟨ π′₂ , π′₁ ⟩

  .idˡ-commutes₁ : π₁ ∘ idˡ ≡ π₁
  idˡ-commutes₁ = begin
                    π₁ ∘ idˡ
                  ≈⟨ sym assoc ⟩ 
                    (π₁ ∘ ⟨ π′₂ , π′₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩′
                  ≈⟨ ∘-resp-≡ˡ p₁.commute₁ ⟩
                    π′₂ ∘ ⟨ π₂ , π₁ ⟩′
                  ≈⟨ p₂.commute₂ ⟩
                    π₁
                  ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .idˡ-commutes₂ : π₂ ∘ idˡ ≡ π₂
  idˡ-commutes₂ = begin
                    π₂ ∘ idˡ
                  ≈⟨ sym assoc ⟩ 
                    (π₂ ∘ ⟨ π′₂ , π′₁ ⟩) ∘ ⟨ π₂ , π₁ ⟩′
                  ≈⟨ ∘-resp-≡ˡ p₁.commute₂ ⟩
                    π′₁ ∘ ⟨ π₂ , π₁ ⟩′
                  ≈⟨ p₂.commute₁ ⟩
                    π₂
                  ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .isoˡ : idˡ ≡ id
  isoˡ = begin
           idˡ
         ≈⟨ sym (p₁.universal idˡ-commutes₁ idˡ-commutes₂) ⟩
           ⟨ π₁ , π₂ ⟩
         ≈⟨ p₁.η ⟩
           id
         ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


  .idʳ-commutes₁ : π′₁ ∘ idʳ ≡ π′₁
  idʳ-commutes₁ = begin
                    π′₁ ∘ idʳ
                  ≈⟨ sym assoc ⟩ 
                    (π′₁ ∘ ⟨ π₂ , π₁ ⟩′) ∘ ⟨ π′₂ , π′₁ ⟩
                  ≈⟨ ∘-resp-≡ˡ p₂.commute₁ ⟩
                    π₂ ∘ ⟨ π′₂ , π′₁ ⟩
                  ≈⟨ p₁.commute₂ ⟩
                    π′₁
                  ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .idʳ-commutes₂ : π′₂ ∘ idʳ ≡ π′₂
  idʳ-commutes₂ = begin
                    π′₂ ∘ idʳ
                  ≈⟨ sym assoc ⟩ 
                    (π′₂ ∘ ⟨ π₂ , π₁ ⟩′) ∘ ⟨ π′₂ , π′₁ ⟩
                  ≈⟨ ∘-resp-≡ˡ p₂.commute₂ ⟩
                    π₁ ∘ ⟨ π′₂ , π′₁ ⟩
                  ≈⟨ p₁.commute₁ ⟩
                    π′₂
                  ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .isoʳ : idʳ ≡ id
  isoʳ = begin
           idʳ
         ≈⟨ sym (p₂.universal idʳ-commutes₁ idʳ-commutes₂) ⟩
           ⟨ π′₁ , π′₂ ⟩′
         ≈⟨ p₂.η ⟩
           id
         ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


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
  
  f : Hom A×[B×C] [A×B]×C
  f = ⟨ ⟨ π₁ , p₂.π₁ ∘ π₂ ⟩p₁ , p₂.π₂ ∘ π₂ ⟩′

  g : Hom [A×B]×C A×[B×C]
  g = ⟨ p₁.π₁ ∘ π′₁ , ⟨ p₁.π₂ ∘ π′₁ , π′₂ ⟩p₂ ⟩
  
  idˡ : Hom A×[B×C] A×[B×C]
  idˡ = g ∘ f

  idʳ : Hom [A×B]×C [A×B]×C
  idʳ = f ∘ g

  .cmˡ₁ : π₁ ∘ idˡ ≡ π₁
  cmˡ₁ = begin 
           π₁ ∘ idˡ
         ≈⟨ sym assoc ⟩
           (π₁ ∘ g) ∘ f
         ≈⟨ ∘-resp-≡ˡ p₃.commute₁ ⟩
           (p₁.π₁ ∘ π′₁) ∘ f
         ≈⟨ assoc ⟩
           p₁.π₁ ∘ (π′₁ ∘ f)
         ≈⟨ ∘-resp-≡ʳ p₄.commute₁ ⟩
           p₁.π₁ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁
         ≈⟨ p₁.commute₁ ⟩
           p₃.π₁
         ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .cmˡ₂₁ : p₂.π₁ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f) ≡ p₂.π₁ ∘ p₃.π₂
  cmˡ₂₁ = begin
           p₂.π₁ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f)
         ≈⟨ sym assoc ⟩
           (p₂.π₁ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂) ∘ f
         ≈⟨ ∘-resp-≡ˡ p₂.commute₁ ⟩
           (p₁.π₂ ∘ p₄.π₁) ∘ f
         ≈⟨ assoc ⟩
           p₁.π₂ ∘ (p₄.π₁ ∘ f)
         ≈⟨ ∘-resp-≡ʳ p₄.commute₁ ⟩
           p₁.π₂ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁
         ≈⟨ p₁.commute₂ ⟩
           p₂.π₁ ∘ p₃.π₂
         ∎
    where
      open SetoidReasoning hom-setoid
      open IsEquivalence equiv  

  .cmˡ₂₂ : p₂.π₂ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f) ≡ p₂.π₂ ∘ p₃.π₂
  cmˡ₂₂ = begin
           p₂.π₂ ∘ (⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f)
         ≈⟨ sym assoc ⟩
           (p₂.π₂ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂) ∘ f
         ≈⟨ ∘-resp-≡ˡ p₂.commute₂ ⟩
           p₄.π₂ ∘ f
         ≈⟨ p₄.commute₂ ⟩
           p₂.π₂ ∘ p₃.π₂
         ∎
    where
      open SetoidReasoning hom-setoid
      open IsEquivalence equiv  

  .cmˡ₂ : π₂ ∘ idˡ ≡ π₂
  cmˡ₂ = begin
           π₂ ∘ idˡ
         ≈⟨ sym assoc ⟩
           (π₂ ∘ g) ∘ f
         ≈⟨ ∘-resp-≡ˡ p₃.commute₂ ⟩
           ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂ ∘ f
         ≈⟨ sym (p₂.universal cmˡ₂₁ cmˡ₂₂) ⟩
           ⟨ p₂.π₁ ∘ p₃.π₂ , p₂.π₂ ∘ p₃.π₂ ⟩p₂
         ≈⟨ p₂.g-η ⟩
           p₃.π₂
         ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv      

  .isoˡ : idˡ ≡ id
  isoˡ = begin
           idˡ
         ≈⟨ sym (p₃.universal cmˡ₁ cmˡ₂) ⟩
           ⟨ π₁ , π₂ ⟩
         ≈⟨ p₃.η ⟩
           id
         ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .cmʳ₁₁ : p₁.π₁ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g) ≡ p₁.π₁ ∘ p₄.π₁
  cmʳ₁₁ = begin
            p₁.π₁ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g)
          ≈⟨ sym assoc ⟩
            (p₁.π₁ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁) ∘ g
          ≈⟨ ∘-resp-≡ˡ p₁.commute₁ ⟩
            p₃.π₁ ∘ g
          ≈⟨ p₃.commute₁ ⟩
            p₁.π₁ ∘ p₄.π₁
          ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .cmʳ₁₂ : p₁.π₂ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g) ≡ p₁.π₂ ∘ p₄.π₁
  cmʳ₁₂ = begin
            p₁.π₂ ∘ (⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g)
          ≈⟨ sym assoc ⟩
            (p₁.π₂ ∘ ⟨ p₃.π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁) ∘ g
          ≈⟨ ∘-resp-≡ˡ p₁.commute₂ ⟩
            (p₂.π₁ ∘ p₃.π₂) ∘ g
          ≈⟨ assoc ⟩
            p₂.π₁ ∘ (p₃.π₂ ∘ g)
          ≈⟨ ∘-resp-≡ʳ p₃.commute₂ ⟩
            p₂.π₁ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂
          ≈⟨ p₂.commute₁ ⟩
            p₁.π₂ ∘ p₄.π₁
          ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


  .cmʳ₁ : π′₁ ∘ idʳ ≡ π′₁
  cmʳ₁ = begin
           π′₁ ∘ idʳ
         ≈⟨ sym assoc ⟩
           (π′₁ ∘ f) ∘ g
         ≈⟨ ∘-resp-≡ˡ p₄.commute₁ ⟩
           ⟨ π₁ , p₂.π₁ ∘ p₃.π₂ ⟩p₁ ∘ g
         ≈⟨ sym (p₁.universal cmʳ₁₁ cmʳ₁₂) ⟩
           ⟨ p₁.π₁ ∘ p₄.π₁ , p₁.π₂ ∘ p₄.π₁ ⟩p₁
         ≈⟨ p₁.g-η ⟩
           π′₁
         ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv

  .cmʳ₂ : π′₂ ∘ idʳ ≡ π′₂
  cmʳ₂ = begin
           π′₂ ∘ idʳ
         ≈⟨ sym assoc ⟩
           (π′₂ ∘ f) ∘ g
         ≈⟨ ∘-resp-≡ˡ p₄.commute₂ ⟩
           (p₂.π₂ ∘ p₃.π₂) ∘ g
         ≈⟨ assoc ⟩
           p₂.π₂ ∘ (p₃.π₂ ∘ g)
         ≈⟨ ∘-resp-≡ʳ p₃.commute₂ ⟩
           p₂.π₂ ∘ ⟨ p₁.π₂ ∘ p₄.π₁ , p₄.π₂ ⟩p₂
         ≈⟨ p₂.commute₂ ⟩
           p₄.π₂
         ∎
    where 
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv
    
  .isoʳ : idʳ ≡ id
  isoʳ = begin
           idʳ
         ≈⟨ sym (p₄.universal cmʳ₁ cmʳ₂) ⟩
           ⟨ π′₁ , π′₂ ⟩′
         ≈⟨ p₄.η ⟩
           id
         ∎
    where
    open SetoidReasoning hom-setoid
    open IsEquivalence equiv


record BinaryProducts : Set (o ⊔ ℓ ⊔ e) where
  field
    product : ∀ {A B} → Product A B

  _×_ : Obj → Obj → Obj
  A × B = Product.A×B (product {A} {B})

  ×-comm : ∀ {A B} → _≅_ C (A × B) (B × A)
  ×-comm = Commutative product product

  ×-assoc : ∀ {X Y Z} → _≅_ C (X × (Y × Z)) ((X × Y) × Z)
  ×-assoc = Associative product product product product
