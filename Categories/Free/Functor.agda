{-# OPTIONS --universe-polymorphism #-}

-- Proof that 'Free' is a functor
module Categories.Free.Functor where

open import Categories.Support.PropositionalEquality

open import Categories.Categories
open import Categories.Category
  renaming (_[_∼_] to _[_~C_])
open import Categories.Free.Core
open import Categories.Functor
  using (Functor)
  renaming (_≡_ to _≡F_; _∘_ to _∘F_)
open import Categories.Graphs
open import Data.Product
open import Graphs.Graph
  renaming (_[_~_] to _[_~G_]; module Heterogeneous to HeterogeneousG)
open import Graphs.GraphMorphism
  renaming (_∘_ to _∘G_)
open import Data.Star
open import Data.Star.Properties
  using (gmap-◅◅; gmap-id)
open import Categories.Support.StarEquality
open import Level using (_⊔_)

ε∼ε : ∀{o₁ ℓ₁ e₁}{X : Graph o₁ ℓ₁ e₁}
       {o₂ ℓ₂ e₂}{Y : Graph o₂ ℓ₂ e₂}
  → (F G : GraphMorphism X Y)
  → F ≈ G
  → {x : Graph.Obj X}
  → Free₀ Y [ ε {x = GraphMorphism.F₀ F x} ~C ε {x = GraphMorphism.F₀ G x} ]
ε∼ε {Y = Y} F G (F≈G₀ , F≈G₁) {x} = ≣-subst (λ z → Free₀ Y [ ε {x = GraphMorphism.F₀ F x} ~C ε {x = z} ]) (F≈G₀ x) (Heterogeneous.refl (Free₀ Y))
-- the below should probably work, but there's an agda bug
-- XXX bug id?  mokus?  anybody?  bueller?
{-
ε∼ε {Y = Y} F G F≈G {x} rewrite proj₁ F≈G x = refl
  where open Heterogeneous (Free₀ Y)
-}

_◅~◅_ : 
  ∀ {o ℓ e}{G : Graph o ℓ e}
    {a₀ a₁ b₀ b₁ c₀ c₁ : Graph.Obj G}
    {f  :       G [ a₀ ↝ b₀ ]}
    {g  :       G [ a₁ ↝ b₁ ]}
    {fs : Free₀ G [ b₀ , c₀ ]}
    {gs : Free₀ G [ b₁ , c₁ ]}
  →       G [ f  ~G g  ]
  → Free₀ G [ fs ~C gs ]
  → Free₀ G [ (f ◅ fs) ~C (g ◅ gs) ]
_◅~◅_ {G = G} (HeterogeneousG.≈⇒~ hd) (Heterogeneous.≡⇒∼ tl)
  = ≡⇒∼ (hd ◅-cong tl)
  where
    open Heterogeneous (Free₀ G)
    open PathEquality G

Free : ∀ {o ℓ e} → Functor (Graphs o ℓ e) (Categories o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e))
Free {o}{ℓ}{e} = record
  { F₀            = Free₀
  ; F₁            = Free₁
  ; identity      = λ {A} f → Heterogeneous.reflexive (Free₀ A) (gmap-id f)
  ; homomorphism  = λ {X}{Y}{Z}{f}{g} → homomorphism {X}{Y}{Z}{f}{g}
  ; F-resp-≡      = λ {X}{Y}{F G : GraphMorphism X Y} → Free₁-resp-≡ {X}{Y}{F}{G}
  }
  where
    module Graphs     = Category (Graphs o ℓ e)
    module Categories = Category (Categories o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e))
    
    .homomorphism : ∀ {X Y Z} {f : GraphMorphism X Y} {g : GraphMorphism Y Z}
                  → Free₁ (g ∘G f) ≡F (Free₁ g ∘F Free₁ f)
    homomorphism ε = Heterogeneous.refl _
    homomorphism {X}{Y}{Z}{f}{g}{S}{U} (_◅_ {.S}{T}{.U} h hs) = 
      HeterogeneousG.refl Z ◅~◅ homomorphism {X}{Y}{Z}{f}{g}{T}{U} hs
    
    .Free₁-resp-≡ : ∀ {X Y} {F G : GraphMorphism X Y} 
      → F ≈ G
      → Free₁ F ≡F Free₁ G
    Free₁-resp-≡ {X}{Y}{F}{G} F≈G {S}{.S} ε = ε∼ε F G F≈G
    Free₁-resp-≡ {X}{Y}{F}{G} F≈G {S}{U} (_◅_ {.S}{T}{.U} h hs) 
      = proj₂ F≈G h ◅~◅ Free₁-resp-≡ {X}{Y}{F}{G} F≈G {T}{U} hs
