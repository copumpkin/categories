{-# OPTIONS --universe-polymorphism #-}

module Categories.NaturalTransformation.Core where

open import Level
open import Relation.Binary using (Rel; IsEquivalence)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Operations
open import Categories.Category
open import Categories.Functor.Core renaming (id to idF)

record NaturalTransformation {o a o′ a′}
                             {C : Category o a}
                             {D : Category o′ a′}
                             (F G : Functor C D) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)

  field
    η : ∀ X → D [ F₀ X , G₀ X ]
    .commute : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

  op : NaturalTransformation G.op F.op
  op = record
    { η = η
    ; commute = λ f → D.Equiv.sym (commute f)
    }

id : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F : Functor C D} → NaturalTransformation F F
id {C = C} {D} {F} = record 
  { η = λ _ → D.id
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  open F

  .commute′ : ∀ {X Y} (f : C [ X , Y ]) → D [ D [ D.id ∘ F₁ f ] ≡ D [ F₁ f ∘ D.id ] ]
  commute′ f = begin
                 D [ D.id ∘ F₁ f ]
               ↓⟨ D.identityˡ ⟩
                 F₁ f
               ↑⟨ D.identityʳ ⟩
                 D [ F₁ f ∘ D.id ]
               ∎
    where 
    open D.HomReasoning

-- "Vertical composition"
_∘₁_ : ∀ {o₀ a₀ o₁ a₁}
        {C : Category o₀ a₀} {D : Category o₁ a₁}
        {F G H : Functor C D}
    → NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘₁_ {C = C} {D} {F} {G} {H} X Y = record 
  { η = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  module H = Functor H
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)
  open H renaming (F₀ to H₀; F₁ to H₁)

  .commute′ : ∀ {A B} (f : C [ A , B ]) → D [ D [ D [ X.η B ∘ Y.η B ] ∘ F₁ f ] ≡ D [ H₁ f ∘ D [ X.η A ∘  Y.η A ] ] ]
  commute′ {A} {B} f = 
           begin
             D [ D [ X.η B ∘ Y.η B ] ∘ F₁ f ]
           ↓⟨ D.assoc ⟩
             D [ X.η B ∘ D [ Y.η B ∘ F₁ f ] ]
           ↓⟨ D.∘-resp-≡ʳ (Y.commute f) ⟩
             D [ X.η B ∘ D [ G₁ f ∘ Y.η A ] ]
           ↑⟨ D.assoc ⟩
             D [ D [ X.η B ∘ G₁ f ] ∘ Y.η A ]
           ↓⟨ D.∘-resp-≡ˡ (X.commute f) ⟩
             D [ D [ H₁ f ∘ X.η A ] ∘ Y.η A ]
           ↓⟨ D.assoc ⟩
             D [ H₁ f ∘ D [ X.η A ∘ Y.η A ] ]
           ∎
    where
    open D.HomReasoning

-- "Horizontal composition"
_∘₀_ : ∀ {o₀ a₀ o₁ a₁ o₂ a₂} 
        {C : Category o₀ a₀} {D : Category o₁ a₁} {E : Category o₂ a₂}
        {F G : Functor C D} {H I : Functor D E}
    → NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘ F) (I ∘ G)
_∘₀_ {C = C} {D} {E} {F} {G} {H} {I} Y X = record 
  { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F₀ q) ]
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  module H = Functor H
  module I = Functor I
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
  open H renaming (F₀ to H₀; F₁ to H₁; F-resp-≡ to H-resp-≡)
  open I renaming (F₀ to I₀; F₁ to I₁; F-resp-≡ to I-resp-≡)

  .commute′ : ∀ {A B} (f : C [ A , B ]) → E [ E [ E [ I₁ (X.η B) ∘ Y.η (F₀ B) ] ∘ H₁ (F₁ f) ] ≡ E [ I₁ (G₁ f) ∘ E [ I₁ (X.η A) ∘ Y.η (F₀ A) ] ] ]
  commute′ {A} {B} f = 
           begin
             E [ E [ I₁ (X.η B) ∘ Y.η (F₀ B) ] ∘ H₁ (F₁ f) ]
           ↓⟨ E.assoc ⟩
             E [ I₁ (X.η B) ∘ E [ Y.η (F₀ B) ∘ H₁ (F₁ f) ] ]
           ↓⟨ E.∘-resp-≡ʳ (Y.commute (F₁ f)) ⟩
             E [ I₁ (X.η B) ∘ E [ I₁ (F₁ f) ∘ Y.η (F₀ A) ] ]
           ↑⟨ E.assoc ⟩
             E [ E [ I₁ (X.η B) ∘ I₁ (F₁ f) ] ∘ Y.η (F₀ A) ]
           ↑⟨ E.∘-resp-≡ˡ I.homomorphism ⟩
             E [ I₁ (D [ X.η B ∘ F₁ f ]) ∘ Y.η (F₀ A) ]
           ↓⟨ E.∘-resp-≡ˡ (I-resp-≡ (X.commute f)) ⟩
             E [ I₁ (D [ G₁ f ∘ X.η A ]) ∘ Y.η (F₀ A) ]
           ↓⟨ E.∘-resp-≡ˡ I.homomorphism ⟩
             E [ E [ I₁ (G₁ f) ∘ I₁ (X.η A) ] ∘ Y.η (F₀ A) ]
           ↓⟨ E.assoc ⟩
             E [ I₁ (G₁ f) ∘ E [ I₁ (X.η A) ∘ Y.η (F₀ A) ] ]
           ∎
    where
    open E.HomReasoning


infix 4 _≡_

_≡_ : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G : Functor C D} → Rel (NaturalTransformation F G) (o ⊔ a′)
_≡_ {D = D} X Y = ∀ {x} → D [ NaturalTransformation.η X x ≡ NaturalTransformation.η Y x ]

promote : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G : Functor C D} (α β : NaturalTransformation F G) → α ≡ β → α ≣ β
promote {C = C} {D} {F} {G} α β α≡β = lemma (≣-ext (λ _ → α≡β))
  where
  module F = Functor F
  module G = Functor G
  module α = NaturalTransformation α
  module β = NaturalTransformation β

  lemma : ∀ {η′} (eq : α.η ≣ η′) → α ≣ record { η = η′; commute = ≣-subst (λ η″ → ∀ {X Y} (f : C [ X , Y ]) → D [ η″ Y ∘ F.F₁ f ] ≣ D [ G.F₁ f ∘ η″ X ]) eq α.commute }
  lemma ≣-refl = ≣-refl

.equiv : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G : Functor C D} → IsEquivalence (_≡_ {F = F} {G})
equiv {C = C} {D} {F} {G} = record 
  { refl = refl
  ; sym = λ f → sym f
  ; trans = λ f g → trans f g
  }
  where
  open Category.Equiv D

setoid : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G : Functor C D} → Setoid _ _
setoid {F = F} {G} = record 
  { Carrier = NaturalTransformation F G
  ; _≈_ = _≡_
  ; isEquivalence = equiv {F = F}
  }
