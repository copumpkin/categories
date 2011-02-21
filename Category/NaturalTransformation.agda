{-# OPTIONS --universe-polymorphism #-}

module Category.NaturalTransformation where

open import Support
open import Category
open import Category.Functor hiding (id) renaming (_∘_ to _∘F_)

record NaturalTransformation {o ℓ e o′ ℓ′ e′}
                             {C : Category o ℓ e}
                             {D : Category o′ ℓ′ e′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    η : ∀ X → D.Hom (F₀ X) (G₀ X)
    .commute : ∀ {X Y} (f : C.Hom X Y) → D.CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

id : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} → NaturalTransformation F F
id {C = C} {D} {F} = record 
  { η = λ _ → D.id
  ; commute = commute′
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F
  open C renaming (_≡_ to _≡C_; _∘_ to _∘C_)
  open D renaming (_≡_ to _≡D_; _∘_ to _∘D_)
  open F

  .commute′ : ∀ {X Y} (f : C.Hom X Y) → (D.id ∘D (F₁ f)) ≡D (F₁ f ∘D D.id)
  commute′ f = begin
                 D.id ∘D (F₁ f)
               ≈⟨ D.identityˡ ⟩
                 F₁ f
               ≈⟨ sym D.identityʳ ⟩
                 F₁ f ∘D D.id
               ∎
    where 
    open IsEquivalence D.equiv
    open SetoidReasoning D.hom-setoid

-- "Vertical composition"
_∘_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁}
        {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁}
        {F G H : Functor C D}
    → NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘_ {C = C} {D} {F} {G} {H} X Y = record 
  { η = λ q → X.η q ∘D Y.η q
  ; commute = commute′
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor F
  module G = Functor G
  module H = Functor H
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  open C renaming (_≡_ to _≡C_; _∘_ to _∘C_)
  open D renaming (_≡_ to _≡D_; _∘_ to _∘D_)
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)
  open H renaming (F₀ to H₀; F₁ to H₁)

  .commute′ : ∀ {A B} (f : C.Hom A B) → ((X.η B ∘D Y.η B) ∘D F₁ f) ≡D (H₁ f ∘D (X.η A ∘D Y.η A))
  commute′ {A} {B} f = 
           begin
             (X.η B ∘D Y.η B) ∘D F₁ f
           ≈⟨ D.assoc ⟩
             X.η B ∘D (Y.η B ∘D F₁ f)
           ≈⟨ D.∘-resp-≡ʳ (Y.commute f) ⟩
             X.η B ∘D (G₁ f ∘D Y.η A)
           ≈⟨ sym D.assoc ⟩
             (X.η B ∘D G₁ f) ∘D Y.η A
           ≈⟨ D.∘-resp-≡ˡ (X.commute f) ⟩
             (H₁ f ∘D X.η A) ∘D Y.η A
           ≈⟨ D.assoc ⟩
             H₁ f ∘D (X.η A ∘D Y.η A)
           ∎
    where
    open IsEquivalence D.equiv
    open SetoidReasoning D.hom-setoid
   
-- "Horizontal composition"
_∘′_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} 
        {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
        {F G : Functor C D} {H I : Functor D E}
    → NaturalTransformation F G → NaturalTransformation H I → NaturalTransformation (H ∘F F) (I ∘F G)
_∘′_ {C = C} {D} {E} {F} {G} {H} {I} X Y = record 
  { η = λ q → I₁ (X.η q) ∘E Y.η (F₀ q)
  ; commute = commute′
  }
  where
  module C = Category.Category C
  module D = Category.Category D
  module E = Category.Category E
  module F = Functor F
  module G = Functor G
  module H = Functor H
  module I = Functor I
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  open C renaming (_≡_ to _≡C_; _∘_ to _∘C_)
  open D renaming (_≡_ to _≡D_; _∘_ to _∘D_)
  open E renaming (_≡_ to _≡E_; _∘_ to _∘E_)
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
  open I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)

  .commute′ : ∀ {A B} (f : C.Hom A B) → ((I₁ (X.η B) ∘E Y.η (F₀ B)) ∘E H₁ (F₁ f)) ≡E (I₁ (G₁ f) ∘E (I₁ (X.η A) ∘E Y.η (F₀ A)))
  commute′ {A} {B} f = 
           begin
             (I₁ (X.η B) ∘E Y.η (F₀ B)) ∘E H₁ (F₁ f)
           ≈⟨ E.assoc ⟩
             I₁ (X.η B) ∘E (Y.η (F₀ B) ∘E H₁ (F₁ f))
           ≈⟨ E.∘-resp-≡ʳ (Y.commute (F₁ f)) ⟩
             I₁ (X.η B) ∘E (I₁ (F₁ f) ∘E Y.η (F₀ A))
           ≈⟨ sym E.assoc ⟩
             (I₁ (X.η B) ∘E I₁ (F₁ f)) ∘E Y.η (F₀ A)
           ≈⟨ E.∘-resp-≡ˡ (IsEquivalence.sym E.equiv I.homomorphism) ⟩
             I₁ (X.η B ∘D F₁ f) ∘E Y.η (F₀ A)
           ≈⟨ E.∘-resp-≡ˡ (I-resp-≡ (X.commute f)) ⟩
             I₁ (G₁ f ∘D X.η A) ∘E Y.η (F₀ A)
           ≈⟨ E.∘-resp-≡ˡ I.homomorphism ⟩
             (I₁ (G₁ f) ∘E I₁ (X.η A)) ∘E Y.η (F₀ A)
           ≈⟨ E.assoc ⟩
             I₁ (G₁ f) ∘E (I₁ (X.η A) ∘E Y.η (F₀ A))
           ∎
    where
    open IsEquivalence E.equiv
    open SetoidReasoning E.hom-setoid
