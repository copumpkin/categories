{-# OPTIONS --universe-polymorphism #-}
module Categories.NaturalTransformation where

open import Categories.Category
open import Categories.Functor hiding (equiv) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.NaturalTransformation.Core public

{-
infixr 9 _∘ˡ_ _∘ʳ_

_∘ˡ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (H : Functor D E) → (η : NaturalTransformation F G) → NaturalTransformation (H ∘F F) (H ∘F G)
_∘ˡ_ {C = C} {D} {E} {F} {G} H η′ = record
  { η       = λ X → Functor.F₁ H (NaturalTransformation.η η′ X)
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
  module E = Category E renaming (_∘_ to _∘E_; _≡_ to _≡E_)
  module H = Functor H
  open D
  open E

  .commute′ : ∀ {X Y} (f : C [ X , Y ]) →
      Functor.F₁ H (NaturalTransformation.η η′ Y) ∘E Functor.F₁ H (Functor.F₁ F f) ≡E
      Functor.F₁ H (Functor.F₁ G f) ∘E Functor.F₁ H (NaturalTransformation.η η′ X)
  commute′ {X} {Y} f =
      begin
        Functor.F₁ H (NaturalTransformation.η η′ Y) ∘E Functor.F₁ H (Functor.F₁ F f)
      ↑⟨ H.homomorphism ⟩
        Functor.F₁ H (NaturalTransformation.η η′ Y ∘D Functor.F₁ F f)
      ↓⟨ H.F-resp-≡ (NaturalTransformation.commute η′ f) ⟩
        Functor.F₁ H (Functor.F₁ G f ∘D NaturalTransformation.η η′ X)
      ↓⟨ H.homomorphism ⟩
        Functor.F₁ H (Functor.F₁ G f) ∘E Functor.F₁ H (NaturalTransformation.η η′ X)
      ∎
    where
    open E.HomReasoning


_∘ʳ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (η : NaturalTransformation F G) → (K : Functor E C) → NaturalTransformation (F ∘F K) (G ∘F K)
_∘ʳ_ η K = record
  { η       = λ X → NaturalTransformation.η η (Functor.F₀ K X)
  ; commute = λ f → NaturalTransformation.commute η (Functor.F₁ K f)
  }



-- The vertical versions
.identity₁ˡ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G}
           → id ∘₁ X ≡ X
identity₁ˡ {D = D} = Category.identityˡ D

.identity₁ʳ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G}
           → X ∘₁ id ≡ X
identity₁ʳ {D = D} = Category.identityʳ D



.assoc₁ : ∀ {o ℓ e o′ ℓ′ e′}
           {P : Category o ℓ e} {Q : Category o′ ℓ′ e′} {A B C D : Functor P Q}
           {X : NaturalTransformation A B} {Y : NaturalTransformation B C} {Z : NaturalTransformation C D}
       → (Z ∘₁ Y) ∘₁ X ≡ Z ∘₁ (Y ∘₁ X)
assoc₁ {Q = Q} = Category.assoc Q


-- The horizontal ones
.identity₀ˡ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G}
           → id {F = idF} ∘₀ X ≡ X
identity₀ˡ {D = D} = Category.identityʳ D

.identity₀ʳ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} {X : NaturalTransformation F G}
           → X ∘₀ id {F = idF} ≡ X
identity₀ʳ {C = C} {D} {F} {G} {X} =
    begin
      G₁ C.id ∘ (η _)
    ↓⟨ ∘-resp-≡ˡ G.identity ⟩
      D.id ∘ (η _)
    ↓⟨ D.identityˡ ⟩
      η _
    ∎
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open NaturalTransformation X
  open D.HomReasoning
  open F
  open G
  open D

-- As of 2.5.4, F and G of _∘₀_ below are no longer inferred
.assoc₀ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
            {C₀ : Category o₀ ℓ₀ e₀} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂} {C₃ : Category o₃ ℓ₃ e₃}
            {F G : Functor C₀ C₁} {H I : Functor C₁ C₂} {J K : Functor C₂ C₃}
        → {X : NaturalTransformation F G} → {Y : NaturalTransformation H I} → {Z : NaturalTransformation J K}
        → (Z ∘₀ Y) ∘₀ X ≡ _∘₀_ {F = H ∘F F} {I ∘F G} Z (Y ∘₀ X)
assoc₀ {C₀ = C₀} {C₁} {C₂} {C₃} {F} {G} {H} {I} {J} {K} {X} {Y} {Z} =
    begin
      K₁ (I₁ (X.η _)) ∘C₃ (K₁ (Y.η (F₀ _)) ∘C₃ Z.η (H₀ (F₀ _)))
    ↑⟨ C₃.assoc ⟩
      (K₁ (I₁ (X.η _)) ∘C₃ K₁ (Y.η (F₀ _))) ∘C₃ Z.η (H₀ (F₀ _))
    ↑⟨ C₃.∘-resp-≡ˡ K.homomorphism ⟩
      (K₁ ((I₁ (X.η _)) ∘C₂ Y.η (F₀ _))) ∘C₃ Z.η (H₀ (F₀ _))
    ∎
  where
  module C₂ = Category C₂ renaming (_∘_ to _∘C₂_; _≡_ to _≡C₂_)
  module C₃ = Category C₃ renaming (_∘_ to _∘C₃_; _≡_ to _≡C₃_)
  module F = Functor F
  module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
  module I = Functor I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)
  module J = Functor J renaming (F₀ to J₀; F₁ to J₁; F-resp-≡ to J-resp-≡)
  module K = Functor K renaming (F₀ to K₀; F₁ to K₁; F-resp-≡ to K-resp-≡)
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  module Z = NaturalTransformation Z
  open C₃.HomReasoning
  open C₂
  open C₃
  open F
  open H
  open I
  open K


.interchange : ∀ {o₀ ℓ₀ e₀} {o₁ ℓ₁ e₁} {o₂ ℓ₂ e₂}
                 {C₀ : Category o₀ ℓ₀ e₀} {C₁ : Category o₁ ℓ₁ e₁} {C₂ : Category o₂ ℓ₂ e₂}
                 {F₀ F₁ F₅ : Functor C₀ C₁} {F₂ F₃ F₄ : Functor C₁ C₂}
                 {α : NaturalTransformation F₃ F₄}
                 {β : NaturalTransformation F₁ F₅}
                 {γ : NaturalTransformation F₂ F₃}
                 {δ : NaturalTransformation F₀ F₁}
             → (α ∘₀ β) ∘₁ (γ ∘₀ δ) ≡ (α ∘₁ γ) ∘₀ (β ∘₁ δ)
interchange {C₀ = C₀} {C₁} {C₂} {F₀} {F₁} {F₅} {F₂} {F₃} {F₄} {α} {β} {γ} {δ} =
    begin
      (F₄.F₁ (β.η _) ∘ α.η (F₁.F₀ _)) ∘ (F₃.F₁ (δ.η _) ∘ γ.η (F₀.F₀ _))
    ↓⟨ C₂.assoc ⟩
      F₄.F₁ (β.η _) ∘ (α.η (F₁.F₀ _) ∘ (F₃.F₁ (δ.η _) ∘ γ.η (F₀.F₀ _)))
    ↑⟨ C₂.∘-resp-≡ʳ C₂.assoc ⟩
      F₄.F₁ (β.η _) ∘ ((α.η (F₁.F₀ _) ∘ (F₃.F₁ (δ.η _))) ∘ γ.η (F₀.F₀ _))
    ↓⟨ C₂.∘-resp-≡ʳ (C₂.∘-resp-≡ˡ (α.commute (δ.η _))) ⟩
      F₄.F₁ (β.η _) ∘ ((F₄.F₁ (δ.η _) ∘ α.η (F₀.F₀ _)) ∘ γ.η (F₀.F₀ _))
    ↓⟨ C₂.∘-resp-≡ʳ C₂.assoc ⟩
      F₄.F₁ (β.η _) ∘ (F₄.F₁ (δ.η _) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _)))
    ↑⟨ C₂.assoc ⟩
      (F₄.F₁ (β.η _) ∘ F₄.F₁ (δ.η _)) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _))
    ↑⟨ C₂.∘-resp-≡ˡ F₄.homomorphism ⟩
      F₄.F₁ (β.η _ ∘C₁ δ.η _) ∘ (α.η (F₀.F₀ _) ∘ γ.η (F₀.F₀ _))
    ∎
  where
  module C₁ = Category C₁ renaming (_∘_ to _∘C₁_; _≡_ to _≡C₁_)
  module C₂ = Category C₂
  module F₀ = Functor F₀
  module F₁ = Functor F₁
  module F₂ = Functor F₂
  module F₃ = Functor F₃
  module F₄ = Functor F₄
  module F₅ = Functor F₅
  module α = NaturalTransformation α
  module β = NaturalTransformation β
  module γ = NaturalTransformation γ
  module δ = NaturalTransformation δ
  open C₁
  open C₂
  open C₂.HomReasoning


.∘₁-resp-≡ : ∀ {o ℓ e} {o′ ℓ′ e′}
               {D : Category o ℓ e} {E : Category o′ ℓ′ e′}
               {A B C : Functor D E}
               {f h : NaturalTransformation B C} {g i : NaturalTransformation A B}
          → f ≡ h → g ≡ i → f ∘₁ g ≡ h ∘₁ i
∘₁-resp-≡ {E = E} f≡h g≡i = Category.∘-resp-≡ E f≡h g≡i

.∘₀-resp-≡ : ∀ {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″}
               {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o″ ℓ″ e″}
               {F F′ : Functor C D} {G G′ : Functor D E}
               {f h : NaturalTransformation G G′} {g i : NaturalTransformation F F′}
           → f ≡ h → g ≡ i → f ∘₀ g ≡ h ∘₀ i
∘₀-resp-≡ {E = E} {G′ = G′} f≡h g≡i = Category.∘-resp-≡ E (Functor.F-resp-≡ G′ g≡i) f≡h
-}
