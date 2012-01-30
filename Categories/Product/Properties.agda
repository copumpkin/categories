{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --universe-polymorphism #-}
open import Level
open import Categories.Category
open import Categories.Product

-- Parameterize over the categories in whose product we are working
module Categories.Product.Properties
    {o ℓ e o′ ℓ′ e′}
    (C : Category o ℓ e)
    (D : Category o′ ℓ′ e′)
    where

C×D : Category _ _ _
C×D = Product C D
module C×D = Category C×D

import Categories.Product.Projections
open Categories.Product.Projections C D

open import Categories.Functor

open import Relation.Binary using (module IsEquivalence)
open import Relation.Binary.PropositionalEquality as PropEq
    using ()
    renaming (_≡_ to _≣_)

∏₁※∏₂≣id : (∏₁ ※ ∏₂) ≣ id
∏₁※∏₂≣id = PropEq.refl

∏₁※∏₂-identity : (∏₁ ※ ∏₂) ≡ id
∏₁※∏₂-identity h = refl
    where open Heterogeneous C×D

※-distrib' :
    ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
    → {A : Category o₁ ℓ₁ e₁}
    → {B : Category o₂ ℓ₂ e₂}
    → {F : Functor B C}
    → {G : Functor B D}
    → {H : Functor A B}
    → ((F ∘ H) ※ (G ∘ H)) ≣ ((F ※ G) ∘ H)
※-distrib' = PropEq.refl

※-distrib : 
    ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
    → {A : Category o₁ ℓ₁ e₁}
    → {B : Category o₂ ℓ₂ e₂}
    → (F : Functor B C)
    → (G : Functor B D)
    → (H : Functor A B)
    → ((F ∘ H) ※ (G ∘ H)) ≡ ((F ※ G) ∘ H)
※-distrib F G H h = refl
    where open Heterogeneous C×D

∏₁※∏₂-distrib : 
    ∀ {o₁ ℓ₁ e₁}{A : Category o₁ ℓ₁ e₁}
    → (F : Functor A C×D)
    → ((∏₁ ∘ F) ※ (∏₂ ∘ F)) ≡ F
∏₁※∏₂-distrib F h = refl
    where open Heterogeneous C×D

module Lemmas where
    open Heterogeneous C×D
    open import Data.Product
    
    lem₁ : {x₁ y₁ x₂ y₂ : Category.Obj C}
        → {x₃ y₃ : Category.Obj D}
        → (f₁ : C [ x₁ , y₁ ])
        → (f₂ : C [ x₂ , y₂ ])
        → (g : D [ x₃ , y₃ ])
        → C   [ f₁ ∼ f₂ ]
        → C×D [ (f₁ , g) ∼ (f₂ , g) ]
    lem₁ f₁ f₂ g (≡⇒∼ f₁≡f₂) = ≡⇒∼ (f₁≡f₂ , Category.Equiv.refl D)
    
    lem₂ : {x₁ y₁ x₂ y₂ : Category.Obj D}
        → {x₃ y₃ : Category.Obj C}
        → (f : C [ x₃ , y₃ ])
        → (g₁ : D [ x₁ , y₁ ])
        → (g₂ : D [ x₂ , y₂ ])
        → D   [ g₁ ∼ g₂ ]
        → C×D [ (f , g₁) ∼ (f , g₂) ]
    lem₂ f g₁ g₂ (≡⇒∼ g₁≡g₂) = ≡⇒∼ (Category.Equiv.refl C , g₁≡g₂)
open Lemmas

※-preserves-≡ˡ :
    ∀ {o₁ ℓ₁ e₁}
    → {A : Category o₁ ℓ₁ e₁}
    → (F₁ : Functor A C)
    → (F₂ : Functor A C)
    → (G  : Functor A D)
    → (F₁ ≡ F₂) → ((F₁ ※ G) ≡ (F₂ ※ G))
※-preserves-≡ˡ F₁ F₂ G F₁≡F₂ h = 
    lem₁ (Functor.F₁ F₁ h) (Functor.F₁ F₂ h) (Functor.F₁ G  h) (F₁≡F₂ h)

※-preserves-≡ʳ :
    ∀ {o₁ ℓ₁ e₁}
    → {A : Category o₁ ℓ₁ e₁}
    → (F  : Functor A C)
    → (G₁ : Functor A D)
    → (G₂ : Functor A D)
    → (G₁ ≡ G₂) → ((F ※ G₁) ≡ (F ※ G₂))
※-preserves-≡ʳ F G₁ G₂ G₁≡G₂ h = 
    lem₂ (Functor.F₁ F h) (Functor.F₁ G₁ h) (Functor.F₁ G₂ h) (G₁≡G₂ h)
    where open Heterogeneous C×D

.※-preserves-≡ :
    ∀ {o₁ ℓ₁ e₁}
    → {A : Category o₁ ℓ₁ e₁}
    → (F : Functor A C)
    → (G : Functor A C)
    → (H : Functor A D)
    → (I : Functor A D)
    → (F ≡ G) → (H ≡ I) → ((F ※ H) ≡ (G ※ I))
※-preserves-≡ {A = A} F G H I F≡G H≡I
    = trans {i = F ※ H}{j = G ※ H}{k = G ※ I}
        (※-preserves-≡ˡ F G H F≡G)
        (※-preserves-≡ʳ G H I H≡I)
    where open IsEquivalence (equiv {C = A}{D = C×D})

.※-universal : 
    ∀ {o₁ ℓ₁ e₁}{A : Category o₁ ℓ₁ e₁}
    → {F : Functor A C}
    → {G : Functor A D}
    → {I : Functor A C×D}
    → (∏₁ ∘ I ≡ F)
    → (∏₂ ∘ I ≡ G)
    → ((F ※ G) ≡ I)
※-universal {_}{_}{_}{A}{F}{G}{I} p₁ p₂ =
    trans {i = F ※ G}{j = (∏₁ ∘ I) ※ (∏₂ ∘ I)}{k = I}
        (sym {i = (∏₁ ∘ I) ※ (∏₂ ∘ I)}{j = F ※ G}
            (※-preserves-≡ (∏₁ ∘ I) F (∏₂ ∘ I) G p₁ p₂))
        (∏₁※∏₂-distrib I)
    where open IsEquivalence (equiv {C = A}{D = C×D})

※-commute₁ : 
    ∀ {o₁ ℓ₁ e₁}{A : Category o₁ ℓ₁ e₁}
    → {F : Functor A C}
    → {G : Functor A D}
    → (∏₁ ∘ (F ※ G) ≡ F)
※-commute₁ h = refl
    where open Heterogeneous C

※-commute₂ : 
    ∀ {o₁ ℓ₁ e₁}{A : Category o₁ ℓ₁ e₁}
    → {F : Functor A C}
    → {G : Functor A D}
    → (∏₂ ∘ (F ※ G) ≡ G)
※-commute₂ h = refl
    where open Heterogeneous D

