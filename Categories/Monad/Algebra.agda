open import Categories.Category
open import Categories.Monad

module Categories.Monad.Algebra {o a} {C : Category o a} (M : Monad C) where

open import Level

module C = Category C
open C using (Obj; _⇒_; _≡_; id; _∘_; CommutativeSquare)

module M = Monad M
open M.F using () renaming (F₀ to M₀; F₁ to M₁)
open M.μ using () renaming (η to μ)
open M.η using (η)

record AlgebraOn (Carrier : Obj) : Set a where
  constructor algebraOn
  private
    X = Carrier
  field
    action      : M₀ X ⇒ X
  private
    f = action
  field
    .{assoc}    : f ∘ M₁ f  ≡ f ∘ (μ X)
    .{identity} : f ∘ (η X) ≡ id

record AlgebraOnMorphism {X₀ Y₀} (X : AlgebraOn X₀) (Y : AlgebraOn Y₀) : Set a where
  constructor alg⇒
  module X = AlgebraOn X
  module Y = AlgebraOn Y

  field
    base       : X₀ ⇒ Y₀
    .{commute} : CommutativeSquare (M₁ base) X.action Y.action base

record Algebra : Set (o ⊔ a) where
  constructor algebra
  field
    {Carrier}   : Obj
  private
    X = Carrier
  field
    action      : M₀ X ⇒ X
  private
    f = action
  field
    .{assoc}    : f ∘ M₁ f  ≡ f ∘ (μ X)
    .{identity} : f ∘ (η X) ≡ id

record AlgebraMorphism (X Y : Algebra) : Set a where
  constructor alg⇒
  module X = Algebra X
  module Y = Algebra Y

  field
    base       : X.Carrier ⇒ Y.Carrier
    .{commute} : CommutativeSquare (M₁ base) X.action Y.action base
