{-# OPTIONS --universe-polymorphism #-}

-- Proof that 'Free' is a functor
module Categories.Free.Functor where

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Categories
open import Categories.Category
  renaming (_[_∼_] to _[_~C_]; _[_,_] to _[_⇒C_])
open import Categories.Free.Core
open import Categories.Functor
  using (Functor; EasyFunctor; Functor-composes)
  renaming (_≡_ to _≡F_)
open import Categories.Quivers
open import Data.Product
open import Graphs.Quiver
  renaming (_[_~_] to _[_~G_]; _[_,_] to _[_⇒G_]
           ; module Heterogeneous to HeterogeneousG)
open import Graphs.Quiver.Morphism
open import Data.Star
open import Data.Star.Properties
  using (gmap-◅◅; gmap-id)
-- open import Categories.Support.StarEquality
open import Level using (_⊔_)

ε∼ε : ∀{o₁ a₁}{X : Quiver o₁ a₁}
       {o₂ a₂}{Y : Quiver o₂ a₂}
  → (F G : QuiverMorphism X Y)
  → F ≈ G
  → {x : Quiver.Obj X}
  → Free₀ Y [ ε {x = QuiverMorphism.F₀ F x} ~C ε {x = QuiverMorphism.F₀ G x} ]
ε∼ε {Y = Y} F G (F≈G₀ , F≈G₁) {x} = ≣-subst (λ z → Free₀ Y [ ε {x = QuiverMorphism.F₀ F x} ~C ε {x = z} ]) (F≈G₀ x) (Heterogeneous.refl (Free₀ Y))
-- the below should probably work, but there's an agda bug
-- XXX bug id?  mokus?  anybody?  bueller?
{-
ε∼ε {Y = Y} F G F≈G {x} rewrite proj₁ F≈G x = refl
  where open Heterogeneous (Free₀ Y)
-}

_◅~◅_ : 
  ∀ {o a}{G : Quiver o a}
    {a₀ a₁ b₀ b₁ c₀ c₁ : Quiver.Obj G}
    {f  :       G [ a₀ ⇒G b₀ ]}
    {g  :       G [ a₁ ⇒G b₁ ]}
    {fs : Free₀ G [ b₀ ⇒C c₀ ]}
    {gs : Free₀ G [ b₁ ⇒C c₁ ]}
  →       G [ f  ~G g  ]
  → Free₀ G [ fs ~C gs ]
  → Free₀ G [ (f ◅ fs) ~C (g ◅ gs) ]
_◅~◅_ {G = G} (HeterogeneousG.≈⇒~ hd) (Heterogeneous.≡⇒∼ tl)
  = ≡⇒∼ (≣-cong₂ _◅_ hd tl)
  where
    open Heterogeneous (Free₀ G)

Freeᵉ : ∀ {o a} → EasyFunctor (Quivers o a) (Categoriesᵉ o (o ⊔ a))
Freeᵉ {o}{a} = record
  { F₀            = Free₀
  ; F₁            = Free₁
  ; identity      = λ {A} f → Heterogeneous.reflexive (Free₀ A) (gmap-id f)
  ; homomorphism  = λ {X}{Y}{Z}{f}{g} → homomorphism {X}{Y}{Z}{f}{g}
  }
  where
    module Graphs     = Category (Quivers o a)
    module Categories = Category (Categories o (o ⊔ a))
    
    .homomorphism : ∀ {X Y Z} {f : QuiverMorphism X Y} {g : QuiverMorphism Y Z}
                  → Free₁ (g ∘ f) ≡F (Free₁ g ∘ Free₁ f)
    homomorphism ε = Heterogeneous.refl _
    homomorphism {X}{Y}{Z}{f}{g}{S}{U} (_◅_ {.S}{T}{.U} h hs) = 
      HeterogeneousG.refl Z ◅~◅ homomorphism {X}{Y}{Z}{f}{g}{T}{U} hs
    
Free : ∀ {o a} → Functor (Quivers o a) (Categories o (o ⊔ a))
Free = EasyFunctor.functor Freeᵉ