{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor where

open import Level
open import Relation.Binary using (IsEquivalence)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_)
open import Categories.Category
open import Categories.Functor.Core public
open import Categories.Morphisms

infix  4 _≡_

-- Evil functor equality
data [_]_∼_ {o ℓ e} (C : Category o ℓ e) {A B} (f : C [ A , B ]) : ∀ {X Y} → C [ X , Y ] → Set (ℓ ⊔ e) where
  refl : {g : C [ A  , B ]} → (f≡g : C [ f ≡ g ]) → [ C ] f ∼ g

_≡_ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (F G : Functor C D) → Set (e′ ⊔ ℓ′ ⊔ ℓ ⊔ o)
_≡_ {C = C} {D} F G = ∀ {A B} → (f : C [ A , B ]) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f


.assoc : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃} 
           {C₀ : Category o₀ ℓ₀ e₀} 
           {C₁ : Category o₁ ℓ₁ e₁} 
           {C₂ : Category o₂ ℓ₂ e₂} 
           {C₃ : Category o₃ ℓ₃ e₃} 
           {F : Functor C₀ C₁} {G : Functor C₁ C₂} {H : Functor C₂ C₃} 
       → (H ∘ G) ∘ F ≡ H ∘ (G ∘ F)
assoc {C₀ = C₀} {C₃ = C₃} {F = F} {G} {H} f = 
  refl {C = C₃} (Functor.F-resp-≡ H (Functor.F-resp-≡ G (Functor.F-resp-≡ F (Category.Equiv.refl C₀))))


.identityˡ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} → id ∘ F ≡ F
identityˡ {C = C} {D} {F} f = refl {C = D} (Functor.F-resp-≡ F (Category.Equiv.refl C))

.identityʳ : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} → F ∘ id ≡ F
identityʳ {C = C} {D} {F} f = refl {C = D} (Functor.F-resp-≡ F (Category.Equiv.refl C))


.equiv : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (_≡_ {C = C} {D = D})
equiv {C = C} {D} = record 
  { refl = λ {F} → refl′ {F}
  ; sym = λ {F} {G} → sym′ {F} {G}
  ; trans = λ {F} {G} {H} → trans′ {F} {G} {H}
  }
  where
  module C = Category C
  module D = Category D

  refl′ : {F : Functor C D} {A B : Category.Obj C} (f : C [ A , B ]) → [ D ] Functor.F₁ F f ∼ Functor.F₁ F f
  refl′ {F} f = refl {C = D} (Functor.F-resp-≡ F (C.Equiv.refl))

  sym′ : {F G : Functor C D} → 
        (∀ {A B} (f : C [ A , B ]) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f) →
        (∀ {A B} (f : C [ A , B ]) → [ D ] Functor.F₁ G f ∼ Functor.F₁ F f)
  sym′ {F} {G} F∼G {A} {B} f = helper (F∼G f)
    where
    helper : ∀ {a b c d} {f : D [ a , b ]} {g : D [ c , d ]}
           → [ D ] f ∼ g → [ D ] g ∼ f
    helper (refl pf) = refl {C = D} (Category.Equiv.sym D pf)

  trans′ : {F G H : Functor C D} →
          (∀ {A B} (f : C [ A , B ]) → [ D ] Functor.F₁ F f ∼ Functor.F₁ G f) →
          (∀ {A B} (f : C [ A , B ]) → [ D ] Functor.F₁ G f ∼ Functor.F₁ H f) →
          (∀ {A B} (f : C [ A , B ]) → [ D ] Functor.F₁ F f ∼ Functor.F₁ H f)
  trans′ {F} {G} {H} F∼G G∼H {A} {B} f = helper (F∼G f) (G∼H f)
    where
    helper : ∀ {a b c d x y} {f : D [ a , b ]} {g : D [ c , d ]} {h : D [ x , y ]}
           → [ D ] f ∼ g → [ D ] g ∼ h → [ D ] f ∼ h
    helper (refl pf₀) (refl pf₁) = refl {C = D} (Category.Equiv.trans D pf₀ pf₁)


.∘-resp-≡  : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
               {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
               {F H : Functor B C} {G I : Functor A B} 
           → F ≡ H → G ≡ I → F ∘ G ≡ H ∘ I
∘-resp-≡ {B = B} {C} {F} {H} {G} {I} F≡H G≡I {P} {Q} q = 
  helper {a = Functor.F₀ G P} {b = Functor.F₀ G Q} {c = Functor.F₀ I P} {d = Functor.F₀ I Q} 
         {f = Functor.F₁ G q}
         {h = Functor.F₁ I q}
         {i = Functor.F₁ H (Functor.F₁ I q)}
         (G≡I q) (F≡H (Functor.F₁ I q))
  where
  module C = Category C
  helper : ∀ {a b c d} {z w}
             {f : B [ a , b ]} {h : B [ c , d ]} 
             {i : C [ z , w ]} 
         → [ B ] f ∼ h → [ C ] (Functor.F₁ F h) ∼ i → [ C ] (Functor.F₁ F f) ∼ i
  helper (refl f≡h) (refl g≡i) = refl {C = C} (Category.Equiv.trans C (Functor.F-resp-≡ F f≡h) g≡i)

Faithful : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Set (o ⊔ ℓ ⊔ e ⊔ e′)
Faithful {C = C} {D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≡ F₁ g ] → C [ f ≡ g ]
  where 
  module C = Category C
  module D = Category D
  open Functor F

-- Is this convoluted double-negated definition really necessary? A naive constructive definition of surjectivity
-- requires a right inverse, which would probably restrict the things we can provide proofs for
Full : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
Full {C = C} {D} F = ∀ {X Y} → ¬ Σ (D [ F₀ X , F₀ Y ]) (λ f → ¬ Σ (C [ X , Y ]) (λ g → D [ F₁ g ≡ f ]))
  where
  module C = Category C
  module D = Category D
  open Functor F

FullyFaithful : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Set (o ⊔ ℓ ⊔ e ⊔ ℓ′ ⊔ e′)
FullyFaithful F = Full F × Faithful F

{-
[02:22:21 AM] <ddarius> copumpkin: So I think the normal statement is fine.  You should be requiring F_1 to be a setoid function, i.e. forall x ~ x'. f(x) ~ f(x').  The function that would be required by the forall y.exists x. ... is not a setoid function and thus doesn't necessarily produce an inverse.  That is, you'll have a function g such that f(g(y)) ~ y but not necessarily f(g(y)) = y and it is not necessary that for y ~ y' that
[02:22:22 AM] <ddarius> g(y) ~ g(y'), they could be different w.r.t. the domain setoid as long as f still maps them to equivalent elements in the codomain.
[02:27:53 AM] <ddarius> For example, let f : 2/= -> 2/~ (where True ~ False).  Then, we need g(True) and g(False) and we could use g = not, even though True /= False and f(g(y)) /= y (assuming say f is id on the carrier), because it is still the case that f(g(y)) ~ y.
[02:28:55 AM] <ddarius> So g isn't an inverse on the carrier sets, and g isn't a setoid function inverse because it's not even a setoid function.
-}

{-
∀ b, ∀ a. f(a) == f(b) → a ≡ b
-}
