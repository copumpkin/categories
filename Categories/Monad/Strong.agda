{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad.Strong where

open import Categories.Category
open import Categories.Monoidal

open import Categories.Functor
  renaming (id to idF; _∘_ to _∘F_; _≡_ to _≡F_)
open import Categories.Functor.Constant
open import Categories.NaturalTransformation
  renaming (id to idN; _≡_ to _≡N_)
open import Categories.NaturalIsomorphism
  using (module NaturalIsomorphism)
open import Categories.Monad

open import Categories.Product

open import Data.Fin using (Fin)
open import Function using (flip)
open import Data.Nat using ()
open import Data.Product using (_,_)
open import Data.Vec 
  using (Vec; _∷_; []; [_]; lookup)

open import Level

record Strength
  {o ℓ e}(C : Category o ℓ e)
  (monoidal : Monoidal C)
  (M : Monad C)
  : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  
  open Monoidal monoidal 
    using (⊗)
    renaming (id to idObj)
  open NaturalIsomorphism (Monoidal.identityˡ monoidal) using () renaming (F⇒G to υˡ)
  open NaturalIsomorphism (Monoidal.identityʳ monoidal) using () renaming (F⇒G to υʳ)
  open NaturalIsomorphism (Monoidal.assoc     monoidal) using ()
    renaming (F⇒G to αʳ; F⇐G to αˡ)
  
  module υˡ = NaturalTransformation υˡ
  open Functor ⊗
    using ()
    renaming (F₀ to ⊗₀; F₁ to ⊗₁)
  
  unitorˡ : ∀ A → ⊗₀ (idObj , A) ⇒ A
  unitorˡ A = υˡ.η (flip lookup [ A ])
  
  associatorʳ : ∀ A B C → ⊗₀ (⊗₀ (A , B) , C) ⇒ ⊗₀ (A , ⊗₀ (B , C))
  associatorʳ A B C = NaturalTransformation.η αʳ (flip lookup (A ∷ B ∷ C ∷ []))
  
  associatorˡ : ∀ A B C → ⊗₀ (A , ⊗₀ (B , C)) ⇒ ⊗₀ (⊗₀ (A , B) , C)
  associatorˡ A B C = NaturalTransformation.η αˡ (flip lookup (A ∷ B ∷ C ∷ []))
      
  
  module M = Monad M
  open M using (F)
  open Functor F
    using (F₀; F₁)
  open NaturalTransformation M.η
    using (η)
  open NaturalTransformation M.μ
    using ()
    renaming (η to μ)
  
  field
    σ : NaturalTransformation (⊗ ∘F (idF {C = C} ⁂ F)) (F ∘F ⊗)
  
  module σ = NaturalTransformation σ
  
  field
    .identity₁ : ∀ {A} 
      → F₁ (unitorˡ A) ∘ σ.η (idObj , A) 
      ≡ unitorˡ (F₀ A)
    
    .identity₂ : ∀ {A B}
      → σ.η (A , B) ∘ ⊗₁ (id , η B)
      ≡ η (⊗₀ (A , B))
    
    α-assoc : ∀ {A B C}
      → F₁ (associatorʳ A B C) ∘ σ.η (⊗₀ (A , B) , C)
      ≡ σ.η (A , ⊗₀ (B , C)) ∘ ⊗₁ (id , σ.η (B , C)) ∘ associatorʳ A B (F₀ C)
    
    μ-assoc : ∀ {A B}
      → μ (⊗₀ (A , B)) ∘ F₁ (σ.η (A , B)) ∘ σ.η (A , F₀ B)
      ≡ σ.η (A , B) ∘ ⊗₁ (id , μ B)
    