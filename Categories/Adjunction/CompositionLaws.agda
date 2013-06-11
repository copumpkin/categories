{-# OPTIONS --universe-polymorphism #-}
module Categories.Adjunction.CompositionLaws where

open import Level

open import Relation.Binary using (Rel; IsEquivalence)
open import Data.Sum
open import Data.Product
open import Function using (flip)

open import Categories.Support.Equivalence
open import Categories.Operations

open import Categories.Category
open import Categories.Functor hiding (equiv; assoc; identityˡ; identityʳ; ∘-resp-≡) renaming (id to idF; _≡_ to _≡F_)
open import Categories.NaturalTransformation hiding (equiv; setoid) renaming (id to idT; _≡_ to _≡T_)
open import Categories.Monad

open import Categories.Adjunction
open import Categories.Adjunction.Composition

.assoc : ∀ {o₀ a₀ o₁ a₁ o₂ a₂ o₃ a₃}
           {C₀ : Category o₀ a₀} {C₁ : Category o₁ a₁} {C₂ : Category o₂ a₂} {C₃ : Category o₃ a₃}
           {F : Functor C₀ C₁} {G : Functor C₁ C₂} {H : Functor C₂ C₃}
           {F′ : Functor C₁ C₀} {G′ : Functor C₂ C₁} {H′ : Functor C₃ C₂}
           {T : F ⊣ F′} {U : G ⊣ G′} {V : H ⊣ H′}
       → (V ∘ U) ∘ T ≡ V ∘ (U ∘ T)
assoc {C₀ = C₀} {C₁} {C₂} {C₃} {F} {G} {H} {F′} {G′} {H′} {T} {U} {V} = (λ {x} → pf₀ {x}) , λ {x} → pf₁ {x}
  where
    module C₀ = Category C₀
    module C₁ = Category C₁
    module C₂ = Category C₂
    module C₃ = Category C₃
    module F = Functor F
    module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    module H = Functor H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
    module F′ = Functor F′ renaming (F₀ to F′₀; F₁ to F′₁; F-resp-≡ to F′-resp-≡)
    module G′ = Functor G′ renaming (F₀ to G′₀; F₁ to G′₁; F-resp-≡ to G′-resp-≡)
    module H′ = Functor H′ renaming (F₀ to H′₀; F₁ to H′₁; F-resp-≡ to H′-resp-≡)
    module T = Adjunction T renaming (unit to Tη′; counit to Tε′)
    module U = Adjunction U renaming (unit to Uη′; counit to Uε′)
    module V = Adjunction V renaming (unit to Vη′; counit to Vε′)
    module Tη = NaturalTransformation (Adjunction.unit T)
    module Tε = NaturalTransformation (Adjunction.counit T)
    module Uη = NaturalTransformation (Adjunction.unit U)
    module Uε = NaturalTransformation (Adjunction.counit U)
    module Vη = NaturalTransformation (Adjunction.unit V)
    module Vε = NaturalTransformation (Adjunction.counit V)

    open C₀ using (Category-composes)
    open C₁ using (Category-composes)
    open C₂ using (Category-composes)
    open C₃ using (Category-composes)

    pf₀ : {x : C₀.Obj} → F′.F′₁ (G′.G′₁ (Vη.η (G.G₀ (F.F₀ x))) ∘ Uη.η (F.F₀ x)) ∘
                           Tη.η x
                           C₀.≡
                           F′.F′₁ (G′.G′₁ (Vη.η (G.G₀ (F.F₀ x)))) ∘
                           F′.F′₁ (Uη.η (F.F₀ x)) ∘ Tη.η x
    pf₀ {x} = begin
               F′.F′₁ (G′.G′₁ (Vη.η (G.G₀ (F.F₀ x))) ∘ Uη.η (F.F₀ x)) ∘
                 Tη.η x
             ↓⟨ C₀.∘-resp-≡ˡ F′.homomorphism ⟩
               (F′.F′₁ (G′.G′₁ (Vη.η (G.G₀ (F.F₀ x)))) ∘
                 F′.F′₁ (Uη.η (F.F₀ x)))
                 ∘ Tη.η x
             ↓⟨ C₀.assoc ⟩
               F′.F′₁ (G′.G′₁ (Vη.η (G.G₀ (F.F₀ x)))) ∘
                 F′.F′₁ (Uη.η (F.F₀ x)) ∘ Tη.η x
             ∎
        where open C₀.HomReasoning

    pf₁ : {x : C₃.Obj} → (Vε.η x ∘ H.H₁ (Uε.η (H′.H′₀ x))) ∘
                               H.H₁ (G.G₁ (Tε.η (G′.G′₀ (H′.H′₀ x))))
                         C₃.≡
                         Vε.η x ∘
                           H.H₁ (Uε.η (H′.H′₀ x) ∘ G.G₁ (Tε.η (G′.G′₀ (H′.H′₀ x))))
    pf₁ {x} = begin
               (Vε.η x ∘ H.H₁ (Uε.η (H′.H′₀ x))) ∘
                 H.H₁ (G.G₁ (Tε.η (G′.G′₀ (H′.H′₀ x))))
             ↓⟨ C₃.assoc ⟩
               Vε.η x ∘
                 H.H₁ (Uε.η (H′.H′₀ x)) ∘ H.H₁ (G.G₁ (Tε.η (G′.G′₀ (H′.H′₀ x))))
             ↑⟨ C₃.∘-resp-≡ʳ H.homomorphism ⟩
               Vε.η x ∘
                 H.H₁ (C₂ [ Uε.η (H′.H′₀ x) ∘ G.G₁ (Tε.η (G′.G′₀ (H′.H′₀ x))) ])
             ∎
      where open C₃.HomReasoning

.identityˡ : ∀ {o a} {o′ a′} {C : Category o a} {D : Category o′ a′} {F : Functor C D} {G : Functor D C} {T : F ⊣ G}
             → id ∘ T ≡ T
identityˡ {C = C} {D} {F} {G} {T} = ( (λ {x} → pf₀ {x}) , D.identityˡ )
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module T = Adjunction T renaming (unit to Tη′; counit to Tε′)
    module Tη = NaturalTransformation T.Tη′
    module Tε = NaturalTransformation T.Tε′

    open C using (Category-composes)

    pf₀ : {x : C.Obj} → G.F₁ D.id ∘ NaturalTransformation.η Tη.op x C.≡
                             NaturalTransformation.η Tη.op x
    pf₀ {x} = begin
               G.F₁ D.id ∘ NaturalTransformation.η Tη.op x
             ↓⟨ C.∘-resp-≡ˡ G.identity ⟩
               C.id ∘ NaturalTransformation.η Tη.op x
             ↓⟨ C.identityˡ ⟩
               NaturalTransformation.η Tη.op x
             ∎
      where open C.HomReasoning

.identityʳ : ∀ {o a} {o′ a′} {C : Category o a} {D : Category o′ a′} {F : Functor C D} {G : Functor D C} {T : F ⊣ G}
             → T ∘ id ≡ T
identityʳ {C = C} {D} {F} {G} {T} = (λ {x} → C.identityʳ) , (λ {x} → pf₀ {x})
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module T = Adjunction T renaming (unit to Tη′; counit to Tε′)
    module Tη = NaturalTransformation T.Tη′
    module Tε = NaturalTransformation T.Tε′

    open D using (Category-composes)

    pf₀ : {x : D.Obj} → NaturalTransformation.η Tε.op x ∘ F.F₁ C.id D.≡
                        NaturalTransformation.η Tε.op x
    pf₀ {x} = begin
               NaturalTransformation.η Tε.op x ∘ F.F₁ C.id
             ↓⟨ D.∘-resp-≡ʳ F.identity ⟩
               NaturalTransformation.η Tε.op x ∘ D.id
             ↓⟨ D.identityʳ ⟩
               NaturalTransformation.η Tε.op x
             ∎
      where open D.HomReasoning

.∘-resp-≡  : ∀ {o₀ a₀ o₁ a₁ o₂ a₂}
               {A : Category o₀ a₀} {B : Category o₁ a₁} {C : Category o₂ a₂}
               {F : Functor B C} {G : Functor A B} {F′ : Functor C B} {G′ : Functor B A}
               {T T′ : G ⊣ G′} {U U′ : F ⊣ F′}
           → T ≡ T′ → U ≡ U′ → U ∘ T ≡ U′ ∘ T′
∘-resp-≡ {A = A} {B} {C} {F} {G} {F′} {G′} {T} {T′} {U} {U′} (Tη≡T′η , Tε≡T′ε) (Uη≡U′η , Uε≡U′ε) =
         (λ {x} → A.∘-resp-≡ (G′.F-resp-≡ Uη≡U′η) Tη≡T′η)
         ,
         (λ {x} → C.∘-resp-≡ Uε≡U′ε (F.F-resp-≡ Tε≡T′ε))
  where
    module A = Category A
    module B = Category B
    module C = Category C
    module F = Functor F
    module G = Functor G
    module F′ = Functor F′
    module G′ = Functor G′
    module T = Adjunction T renaming (unit to Tη′; counit to Tε′)
    module U = Adjunction U renaming (unit to Uη′; counit to Uε′)
    module T′ = Adjunction T′ renaming (unit to T′η′; counit to T′ε′)
    module U′ = Adjunction U′ renaming (unit to U′η′; counit to U′ε′)
    module Tη = NaturalTransformation (Adjunction.unit T)
    module Tε = NaturalTransformation (Adjunction.counit T)
    module Uη = NaturalTransformation (Adjunction.unit U)
    module Uε = NaturalTransformation (Adjunction.counit U)
    module T′η = NaturalTransformation (Adjunction.unit T′)
    module T′ε = NaturalTransformation (Adjunction.counit T′)
    module U′η = NaturalTransformation (Adjunction.unit U′)
    module U′ε = NaturalTransformation (Adjunction.counit U′)
