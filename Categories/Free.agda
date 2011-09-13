{-# OPTIONS --universe-polymorphism #-}

module Categories.Free where

open import Categories.Category
open import Categories.Free.Core
open import Categories.Free.Functor
open import Categories.Graphs.Underlying
open import Categories.Functor
  using (Functor)
open import Graphs.Graph
open import Graphs.GraphMorphism
  using (GraphMorphism; module GraphMorphism)
open import Data.Star

-- Exports from other modules:
--    Free₀, Free₁ and Free
open Categories.Free.Core public
  using (Free₀)
open Categories.Free.Functor public
  using (Free)

-- TODO:
--  Prove Free⊣Underlying : Adjunction Free Underlying
--  Define Adjunction.left and Adjunction.right as conveniences
--    (or whatever other names make sense for the hom-set maps
--    C [ F _ , _ ] → D [ _ , G _ ] and inverse, respectively)
--  Let Cata = Adjunction.left Free⊣Underlying
Cata : ∀{o₁ ℓ₁ e₁}{G : Graph    o₁ ℓ₁ e₁}
        {o₂ ℓ₂ e₂}{C : Category o₂ ℓ₂ e₂}
  → (F : GraphMorphism G (Underlying₀ C))
  → Functor (Free₀ G) C
Cata {G = G} {C = C} F = record
  { F₀            = F₀
  ; F₁            = F₁*
  ; identity      = refl
  ; homomorphism  = λ{X}{Y}{Z}{f}{g} → homomorphism {X}{Y}{Z}{f}{g}
  ; F-resp-≡      = F₁*-resp-≡
  }
  where
    open Category C
    open GraphMorphism F
    open Equiv
    open HomReasoning
    open PathEquality using (ε-cong; _◅-cong_)
    
    F₁* : ∀ {A B} → Free₀ G [ A , B ] → C [ F₀ A , F₀ B ]
    F₁* ε = id
    F₁* (f ◅ fs) = F₁* fs ∘ F₁ f
    
    .homomorphism : ∀ {X Y Z} {f : Free₀ G [ X , Y ]} {g : Free₀ G [ Y , Z ]}
                  → C [ F₁* (Free₀ G [ g ∘ f ]) ≡ C [ F₁* g ∘ F₁* f ] ]
    homomorphism {f = ε} = sym identityʳ
    homomorphism {f = f ◅ fs}{gs} =
      begin
        F₁* (fs ◅◅ gs) ∘ F₁ f
      ↓⟨ homomorphism {f = fs}{gs} ⟩∘⟨ refl ⟩
        (F₁* gs ∘ F₁* fs) ∘ F₁ f
      ↓⟨ assoc ⟩
        F₁* gs ∘ F₁* fs ∘ F₁ f
      ∎
    
    .F₁*-resp-≡ : ∀ {A B} {f g : Free₀ G [ A , B ]} → Free₀ G [ f ≡ g ] → C [ F₁* f ≡ F₁* g ]
    F₁*-resp-≡ {f = ε}{.ε} ε-cong = refl
    F₁*-resp-≡ {f = f ◅ fs}{g ◅ gs} (f≈g ◅-cong fs≈gs) = 
      begin
        F₁* fs ∘ F₁ f
      ↓⟨ F₁*-resp-≡ fs≈gs ⟩∘⟨ F-resp-≈ f≈g ⟩
        F₁* gs ∘ F₁ g
      ∎
    F₁*-resp-≡ {f = f ◅ fs}{ε} ()
