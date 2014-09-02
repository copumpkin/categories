module Categories.Functor.Discrete where

open import Categories.Category
open import Categories.Functor
open import Categories.Agda
open import Categories.Categories
open import Categories.Support.PropositionalEquality
import Categories.Discrete as D

Discrete : ∀ {o} -> Functor (Sets o) (Categories o o _)
Discrete {o} = record {
             F₀ = D.Discrete;
             F₁ = F₁;
             identity = λ f → Heterogeneous.≡⇒∼ _;
             homomorphism = λ f → Heterogeneous.≡⇒∼ _;
             F-resp-≡ = F-resp-≡}
  where
    F₁ : {A B : Category.Obj (Sets o)} → Sets o [ A , B ] →
                        Categories o o _ [ D.Discrete A , D.Discrete B ]
    F₁ f = record {
             F₀ = f;
             F₁ = ≣-cong f;
             identity = _;
             homomorphism = _;
             F-resp-≡ = _ }
  
    F-resp-≡ : {A B : Set o} {F G : Sets o [ A , B ]} →
                  Sets o [ F ≡ G ] → Categories o o _ [ F₁ F ≡ F₁ G ]
    F-resp-≡ F≡G {a} ≣-refl rewrite F≡G {a} = Heterogeneous.≡⇒∼ _
