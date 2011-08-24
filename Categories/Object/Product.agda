{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Product {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Function using (flip)
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
  
  private
    .lem : 
      ∀{W X Y Z}{f : Y ⇒ Z}{g : X ⇒ Y}{h : X ⇒ Z}{i : W ⇒ X}
      → f ∘ g ≡ h
      → f ∘ (g ∘ i) ≡ h ∘ i
    lem {W}{X}{Y}{Z}{f}{g}{h}{i} commute =
      trans (sym assoc) (∘-resp-≡ commute refl)
  
  .⟨⟩-distrib-∘ : ∀ {C D}{f : C ⇒ D}{g : D ⇒ A}{h : D ⇒ B}
    → ⟨ g , h ⟩ ∘ f ≡ ⟨ g ∘ f , h ∘ f ⟩
  ⟨⟩-distrib-∘ {C}{D}{f}{g}{h} 
    = sym (universal (lem commute₁) (lem commute₂))

[_⇒_]_⁂_ : ∀ {W X Y Z}
    → (W×Y : Product W Y)
    → (X×Z : Product X Z)
    → (W ⇒ X) → (Y ⇒ Z) → (Product.A×B W×Y ⇒ Product.A×B X×Z)
[_⇒_]_⁂_ W×Y X×Z f g = X×Z.⟨_,_⟩ (f ∘ W×Y.π₁) (g ∘ W×Y.π₂)
    where
        module W×Y = Product W×Y
        module X×Z = Product X×Z

[_⇒_]first 
    : ∀ {X Y Z}
    → (X×Z : Product X Z) → (Y×Z : Product Y Z)
    → X ⇒ Y → Product.A×B X×Z ⇒ Product.A×B Y×Z
[_⇒_]first X×Z Y×Z f = [ X×Z ⇒ Y×Z ] f ⁂ id

[_⇒_]second
    : ∀ {X Y Z}
    → (X×Y : Product X Y) → (X×Z : Product X Z)
    → Y ⇒ Z → Product.A×B X×Y ⇒ Product.A×B X×Z
[_⇒_]second X×Y X×Z g = [ X×Y ⇒ X×Z ] id ⁂ g

open import Categories.Morphisms

convert : ∀ {A B} → (p₁ : Product A B) (p₂ : Product A B) → Product.A×B p₁ ⇒ Product.A×B p₂
convert p₁ p₂ = p₂.⟨_,_⟩ p₁.π₁ p₁.π₂
  where
  module p₁ = Product p₁
  module p₂ = Product p₂

convert-Iso : ∀ {A B} → (p₁ : Product A B) (p₂ : Product A B) → Iso C (convert p₁ p₂) (convert p₂ p₁)
convert-Iso p₁ p₂ = record
  { isoˡ = isoˡ
  ; isoʳ = isoʳ
  }
  where
  module p₁ = Product p₁
  module p₂ = Product p₂
  open Product p₁
  open Product p₂ renaming (π₁ to π′₁; π₂ to π′₂; ⟨_,_⟩ to ⟨_,_⟩′)
  open HomReasoning

  .isoˡ : ⟨ π′₁ , π′₂ ⟩ ∘ ⟨ π₁ , π₂ ⟩′ ≡ id
  isoˡ = begin
           ⟨ π′₁ , π′₂ ⟩ ∘ ⟨ π₁ , π₂ ⟩′
         ↓⟨ p₁.⟨⟩-distrib-∘ ⟩
           ⟨ π′₁ ∘ ⟨ π₁ , π₂ ⟩′ , π′₂ ∘ ⟨ π₁ , π₂ ⟩′ ⟩
         ↓⟨ p₁.⟨⟩-cong₂ p₂.commute₁ p₂.commute₂ ⟩
           ⟨ π₁ , π₂ ⟩
         ↓⟨ p₁.η ⟩
           id
         ∎

  .isoʳ : ⟨ π₁ , π₂ ⟩′ ∘ ⟨ π′₁ , π′₂ ⟩ ≡ id
  isoʳ = begin
           ⟨ π₁ , π₂ ⟩′ ∘ ⟨ π′₁ , π′₂ ⟩
         ↓⟨ p₂.⟨⟩-distrib-∘ ⟩
           ⟨ π₁ ∘ ⟨ π′₁ , π′₂ ⟩ , π₂ ∘ ⟨ π′₁ , π′₂ ⟩ ⟩′
         ↓⟨ p₂.⟨⟩-cong₂ p₁.commute₁ p₁.commute₂ ⟩
           ⟨ π′₁ , π′₂ ⟩′
         ↓⟨ p₂.η ⟩
           id
         ∎

Unique : ∀ {A B} → (p₁ : Product A B) (p₂ : Product A B) → _≅_ C (Product.A×B p₁) (Product.A×B p₂)
Unique p₁ p₂ = record
  { f = convert p₁ p₂
  ; g = convert p₂ p₁
  ; iso = convert-Iso p₁ p₂
  }

Swap : ∀ {A B} → Product A B → Product B A
Swap p = record
  { A×B       = p.A×B
  ; π₁        = p.π₂
  ; π₂        = p.π₁
  ; ⟨_,_⟩     = flip p.⟨_,_⟩
  ; commute₁  = p.commute₂
  ; commute₂  = p.commute₁
  ; universal = flip p.universal
  } where module p = Product p

Commutative : ∀ {A B} → (p₁ : Product A B) (p₂ : Product B A) → _≅_ C (Product.A×B p₁) (Product.A×B p₂)
Commutative p₁ p₂ = Unique (Swap p₁) p₂

Twist : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) → Product (Product.A×B p₁) Z
Twist {X}{Y}{Z} p₁ p₂ p₃ = record
  { A×B       = p₃.A×B
  ; π₁        = π₁
  ; π₂        = π₂
  ; ⟨_,_⟩     = ⟨_,_⟩
  ; commute₁  = commute₁
  ; commute₂  = commute₂
  ; universal = λ h₁ h₂ → p₃.universal (universal₁ h₁) (universal₂ h₁ h₂)
  } where
  module p₁ = Product p₁
  module p₂ = Product p₂
  module p₃ = Product p₃
  
  π₁    = p₁.⟨_,_⟩ p₃.π₁ (p₂.π₁ ∘ p₃.π₂)
  π₂    = p₂.π₂ ∘ p₃.π₂
  ⟨_,_⟩ : ∀ {C} → (C ⇒ p₁.A×B) → (C ⇒ Z) → (C ⇒ p₃.A×B)
  ⟨ f , g ⟩ = p₃.⟨_,_⟩ (p₁.π₁ ∘ f) (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g)
  
  open HomReasoning
  
  -- these proofs look a lot worse than they are; they're
  -- very straightforward projection-shufflings
  
  .interchange : ∀ {C} {f : C ⇒ p₁.A×B} {g : C ⇒ Z}
    → (p₂.π₁ ∘ p₃.π₂) ∘ ⟨ f , g ⟩ ≡ p₁.π₂ ∘ f
  interchange {C}{f}{g} =
    begin
      (p₂.π₁ ∘ p₃.π₂) ∘ (p₃.⟨_,_⟩ (p₁.π₁ ∘ f) (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g))
    ↓⟨ assoc ⟩
      p₂.π₁ ∘ (p₃.π₂ ∘ (p₃.⟨_,_⟩ (p₁.π₁ ∘ f) (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g)))
    ↓⟨ refl ⟩∘⟨ p₃.commute₂ ⟩
      p₂.π₁ ∘ (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g)
    ↓⟨ p₂.commute₁ ⟩
      p₁.π₂ ∘ f
    ∎
  
  .commute₁ : ∀ {C} {f : C ⇒ p₁.A×B} {g : C ⇒ Z} → π₁ ∘ ⟨ f , g ⟩ ≡ f
  commute₁ {C}{f}{g} = 
    begin
      p₁.⟨_,_⟩ p₃.π₁ (p₂.π₁ ∘ p₃.π₂) ∘ ⟨ f , g ⟩
    ↓⟨ p₁.⟨⟩-distrib-∘ ⟩
      p₁.⟨_,_⟩ (p₃.π₁ ∘ ⟨ f , g ⟩) ((p₂.π₁ ∘ p₃.π₂) ∘ ⟨ f , g ⟩)
    ↓⟨ p₁.⟨⟩-cong₂ p₃.commute₁ interchange ⟩
      p₁.⟨_,_⟩ (p₁.π₁ ∘ f) (p₁.π₂ ∘ f)
    ↓⟨ p₁.g-η ⟩
      f
    ∎

  .commute₂ : ∀ {C} {f : C ⇒ p₁.A×B} {g : C ⇒ Z} → π₂ ∘ ⟨ f , g ⟩ ≡ g
  commute₂ {C}{f}{g} = 
    begin
      (p₂.π₂ ∘ p₃.π₂) ∘ (p₃.⟨_,_⟩ (p₁.π₁ ∘ f) (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g))
    ↓⟨ assoc ⟩
      p₂.π₂ ∘ (p₃.π₂ ∘ (p₃.⟨_,_⟩ (p₁.π₁ ∘ f) (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g)))
    ↓⟨ refl ⟩∘⟨ p₃.commute₂ ⟩
      p₂.π₂ ∘ (p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g)
    ↓⟨ p₂.commute₂ ⟩
      g
    ∎
  
  -- split h over p₁ using one of p₁'s "commute" laws
  .split : ∀ {C D} {π : p₁.A×B ⇒ D} {π′ : p₃.A×B ⇒ D} {f : C ⇒ p₁.A×B} {i : C ⇒ p₃.A×B}
    → π ∘ π₁ ≡ π′
    → π₁ ∘ i ≡ f
    → π′ ∘ i ≡ π ∘ f
  split {C}{D}{π}{π′}{f}{i} commute h = 
    begin
      π′ ∘ i
    ↑⟨ commute ⟩∘⟨ refl ⟩
      (π ∘ π₁) ∘ i
    ↓⟨ assoc ⟩
      π ∘ (π₁ ∘ i)
    ↓⟨ refl ⟩∘⟨ h ⟩
      π ∘ f
    ∎
  
  .universal₁ : ∀ {C} {f : C ⇒ p₁.A×B} {i : C ⇒ p₃.A×B}
    → π₁ ∘ i ≡ f
    → p₃.π₁ ∘ i ≡ p₁.π₁ ∘ f
  universal₁ h₁
    = split p₁.commute₁ h₁
  
  .universal₂ : ∀ {C} {f : C ⇒ p₁.A×B} {g : C ⇒ Z} {i : C ⇒ p₃.A×B}
    → π₁ ∘ i ≡ f
    → π₂ ∘ i ≡ g 
    → p₃.π₂ ∘ i ≡ p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g
  universal₂ {C}{f}{g}{i} h₁ h₂ =
    begin
      p₃.π₂ ∘ i
    ↑⟨ p₂.g-η ⟩
      p₂.⟨_,_⟩ (p₂.π₁ ∘ (p₃.π₂ ∘ i)) (p₂.π₂ ∘ (p₃.π₂ ∘ i))
    ↑⟨ p₂.⟨⟩-cong₂ assoc assoc ⟩
      p₂.⟨_,_⟩ ((p₂.π₁ ∘ p₃.π₂) ∘ i) ((p₂.π₂ ∘ p₃.π₂) ∘ i)
    ↓⟨ p₂.⟨⟩-cong₂ (split p₁.commute₂ h₁) h₂ ⟩
      p₂.⟨_,_⟩ (p₁.π₂ ∘ f) g
    ∎

Associative : ∀ {X Y Z} (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) → _≅_ C (Product.A×B p₃) (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = Unique (Twist p₁ p₂ p₃) p₄
