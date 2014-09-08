module Categories.Monad.Cartesian where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Monad
open import Categories.Pullback

-- should this get its own module?
Equifibrant : ∀ {o a} {o′ a′} {C : Category o a} {D : Category o′ a′}
                {F G : Functor C D} (η : NaturalTransformation F G)
              → Set (o ⊔ a ⊔ o′ ⊔ a′)
Equifibrant {C = C} {D} {F} {G} η = ∀ {X Y} (f : C [ X , Y ])
                                    → PullbackSquare D (F₁ f) (η.η X)
                                                       (η.η Y) (G₁ f)
  where
  open Functor F using (F₁)
  open Functor G using () renaming (F₁ to G₁)
  module η = NaturalTransformation η

record CartesianMonad {o a} (C : Category o a) : Set (o ⊔ a) where
  field
    monad : Monad C
  open Monad monad public

  open Category C
  open Functor F
  field
    preserves : ∀ {P X Y Z} (p₁ : P ⇒ X) (p₂ : P ⇒ Y) (f : X ⇒ Z) (g : Y ⇒ Z)
                → PullbackSquare C p₁ p₂ f g
                → PullbackSquare C (F₁ p₁) (F₁ p₂) (F₁ f) (F₁ g)
    η-equifibrant : Equifibrant η
    μ-equifibrant : Equifibrant μ
