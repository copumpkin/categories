{-# OPTIONS --universe-polymorphism #-}
module Categories.Category where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive) renaming (_⇒_ to _⊆_)
open import Function using (flip)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning
open import Data.Product

postulate
  .irr : ∀ {a} {A : Set a} → .A → A

record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where 
  eta-equality
  infix  4 _≡_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    {_≡_} : ∀ {A B} → Rel (A ⇒ B) e

    {id}  : ∀ {A} → (A ⇒ A)
    {_∘_} : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    .{assoc}     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    .{identityˡ} : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    .{identityʳ} : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    .{equiv}     : ∀ {A B} → IsEquivalence (_≡_ {A} {B})
    .{∘-resp-≡}  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

  -- with irrelevant modules this would be:
  -- module .Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})
  module Equiv {A B : Obj} where
    module e = IsEquivalence
    private
      .q : IsEquivalence _≡_
      q = equiv {A} {B}

    .refl : Reflexive _≡_
    refl = e.refl q
    .trans : Transitive _≡_
    trans = e.trans q
    .sym : Symmetric _≡_
    sym = e.sym q
    .reflexive : _≣_ ⊆ _≡_
    reflexive = e.reflexive q

  open Equiv

  domain : ∀ {A B} → (A ⇒ B) → Obj
  domain {A} _ = A

  codomain : ∀ {A B} → (A ⇒ B) → Obj
  codomain {B = B} _ = B

  .∘-resp-≡ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≡ h → f ∘ g ≡ h ∘ g
  ∘-resp-≡ˡ pf = ∘-resp-≡ pf refl

  .∘-resp-≡ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≡ h → g ∘ f ≡ g ∘ h
  ∘-resp-≡ʳ pf = ∘-resp-≡ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record 
    { Carrier = A ⇒ B
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }

  module HomReasoning {A B : Obj} where
    open SetoidReasoning (hom-setoid {A} {B}) public

    infixr 4 _⟩∘⟨_
    ._⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
    _⟩∘⟨_ = ∘-resp-≡

  op : Category o ℓ e
  op = record 
    { Obj = Obj
    ; _⇒_ = flip _⇒_
    ; _≡_ = _≡_
    ; _∘_ = flip _∘_
    ; id = id
    ; assoc = sym assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; equiv = record 
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    ; ∘-resp-≡ = flip ∘-resp-≡
    }

  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≡ i ∘ g


  .id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≡ g) → f ≡ id
  id-unique g∘f≡g = trans (sym identityˡ) (g∘f≡g id)

  .id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ id ∘ f
  id-comm = trans identityʳ (sym identityˡ)

infix 10  _[_,_] _[_≡_] _[_∘_]

_[_,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_≡_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≡_] = Category._≡_

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

-- Should this live in the Category record itself? It doesn't seem terribly useful for most situations
module Heterogeneous {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open Equiv renaming (refl to refl′; sym to sym′; trans to trans′; reflexive to reflexive′)

  infix 4 _∼_

  data _∼_ {A B} (f : A ⇒ B) : ∀ {X Y} → (X ⇒ Y) → Set (ℓ ⊔ e) where
    ≡⇒∼ : {g : A ⇒ B} → .(f ≡ g) → f ∼ g

  refl : ∀ {A B} {f : A ⇒ B} → f ∼ f
  refl = ≡⇒∼ refl′

  sym : ∀ {A B} {f : A ⇒ B} {D E} {g : D ⇒ E} → f ∼ g → g ∼ f
  sym (≡⇒∼ f≡g) = ≡⇒∼ (sym′ f≡g)

  trans : ∀ {A B} {f : A ⇒ B} 
             {D E} {g : D ⇒ E}
             {F G} {h : F ⇒ G}
          → f ∼ g → g ∼ h → f ∼ h
  trans (≡⇒∼ f≡g) (≡⇒∼ g≡h) = ≡⇒∼ (trans′ f≡g g≡h)

  reflexive : ∀ {A B} {f g : A ⇒ B} → f ≣ g → f ∼ g
  reflexive f≣g = ≡⇒∼ (reflexive′ f≣g)

  ∘-resp-∼ : ∀ {A B C A′ B′ C′} {f : B ⇒ C} {h : B′ ⇒ C′} {g : A ⇒ B} {i : A′ ⇒ B′} → f ∼ h → g ∼ i → (f ∘ g) ∼ (h ∘ i)
  ∘-resp-∼ (≡⇒∼ f≡h) (≡⇒∼ g≡i) = ≡⇒∼ (∘-resp-≡ f≡h g≡i)

  ∘-resp-∼ˡ : ∀ {A B C C′} {f : B ⇒ C} {h : B ⇒ C′} {g : A ⇒ B} → f ∼ h → (f ∘ g) ∼ (h ∘ g)
  ∘-resp-∼ˡ (≡⇒∼ f≡h) = ≡⇒∼ (∘-resp-≡ˡ f≡h)

  ∘-resp-∼ʳ : ∀ {A A′ B C} {f : A ⇒ B} {h : A′ ⇒ B} {g : B ⇒ C} → f ∼ h → (g ∘ f) ∼ (g ∘ h)
  ∘-resp-∼ʳ (≡⇒∼ f≡h) = ≡⇒∼ (∘-resp-≡ʳ f≡h)

  .∼⇒≡ : ∀ {A B} {f g : A ⇒ B} → f ∼ g → f ≡ g
  ∼⇒≡ (≡⇒∼ f≡g) = irr f≡g

  
  domain-≣ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → A ≣ A′
  domain-≣ (≡⇒∼ _) = ≣-refl

  codomain-≣ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → B ≣ B′
  codomain-≣ (≡⇒∼ _) = ≣-refl

  ∼-cong : ∀ {t : Level} {T : Set t} {dom cod : T → Obj} (f : (x : T) → dom x ⇒ cod x) → ∀ {i j} (eq : i ≣ j) → f i ∼ f j
  ∼-cong f ≣-refl = refl

  -- floating morphisms on ≣
  float₂ : ∀ {A A′ B B′} → A ≣ A′ → B ≣ B′ → A ⇒ B → A′ ⇒ B′
  float₂ = ≣-subst₂ _⇒_

  relaxed : ∀ {A B} {f : A ⇒ B} {X Y} {g : X ⇒ Y} -> (A≣X : A ≣ X) (B≣Y : B ≣ Y) -> float₂ A≣X B≣Y f ≡ g -> f ∼ g   
  relaxed ≣-refl ≣-refl f≡g = ≡⇒∼ f≡g 

  floatˡ : ∀ {A B B′} → B ≣ B′ → A ⇒ B → A ⇒ B′
  floatˡ {A} = ≣-subst (_⇒_ A)

  floatˡ-resp-trans : ∀ {A B B′ B″} (B≣B′ : B ≣ B′) (B′≣B″ : B′ ≣ B″) (f : A ⇒ B) → floatˡ (≣-trans B≣B′ B′≣B″) f ≣ floatˡ B′≣B″ (floatˡ B≣B′ f)
  floatˡ-resp-trans {A} = ≣-subst-trans (_⇒_ A)

  floatʳ : ∀ {A A′ B} → A ≣ A′ → A ⇒ B → A′ ⇒ B
  floatʳ {B = B} = ≣-subst (λ X → X ⇒ B)

  float₂-breakdown-lr : ∀ {A A′} (A≣A′ : A ≣ A′) {B B′} (B≣B′ : B ≣ B′) (f : A ⇒ B) → float₂ A≣A′ B≣B′ f ≣ floatˡ B≣B′ (floatʳ A≣A′ f)
  float₂-breakdown-lr = ≣-subst₂-breakdown-lr _⇒_

  float₂-breakdown-rl : ∀ {A A′} (A≣A′ : A ≣ A′) {B B′} (B≣B′ : B ≣ B′) (f : A ⇒ B) → float₂ A≣A′ B≣B′ f ≣ floatʳ A≣A′ (floatˡ B≣B′ f)
  float₂-breakdown-rl = ≣-subst₂-breakdown-rl _⇒_
  
  -- henry ford versions
  .∼⇒≡₂ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → (A≣A′ : A ≣ A′) (B≣B′ : B ≣ B′) → float₂ A≣A′ B≣B′ f ≡ f′
  ∼⇒≡₂ pf ≣-refl ≣-refl = ∼⇒≡ pf

  .∼⇒≡ˡ : ∀ {A B B′} {f : A ⇒ B} {f′ : A ⇒ B′} → f ∼ f′ → (B≣B′ : B ≣ B′) → floatˡ B≣B′ f ≡ f′
  ∼⇒≡ˡ pf ≣-refl = ∼⇒≡ pf

  .∼⇒≡ʳ : ∀ {A A′ B} {f : A ⇒ B} {f′ : A′ ⇒ B} → f ∼ f′ → (A≣A′ : A ≣ A′) → floatʳ A≣A′ f ≡ f′
  ∼⇒≡ʳ pf ≣-refl = ∼⇒≡ pf

  ≡⇒∼ʳ : ∀ {A A′ B} {f : A ⇒ B} {f′ : A′ ⇒ B} → (A≣A′ : A ≣ A′) → .(floatʳ A≣A′ f ≡ f′) → f ∼ f′
  ≡⇒∼ʳ ≣-refl pf = ≡⇒∼ pf

  float₂-resp-∼ : ∀ {A A′ B B′} (A≣A′ : A ≣ A′) (B≣B′ : B ≣ B′) {f : C [ A , B ]} → f ∼ float₂ A≣A′ B≣B′ f
  float₂-resp-∼ ≣-refl ≣-refl = refl

  floatˡ-resp-∼ : ∀ {A B B′} (B≣B′ : B ≣ B′) {f : C [ A , B ]} → f ∼ floatˡ B≣B′ f
  floatˡ-resp-∼ ≣-refl = refl

  floatʳ-resp-∼ : ∀ {A A′ B} (A≣A′ : A ≣ A′) {f : C [ A , B ]} → f ∼ floatʳ A≣A′ f
  floatʳ-resp-∼ ≣-refl = refl
  
_[_∼_] : ∀ {o ℓ e} (C : Category o ℓ e) {A B} (f : C [ A , B ]) {X Y} (g : C [ X , Y ]) → Set (ℓ ⊔ e)
C [ f ∼ g ] = Heterogeneous._∼_ C f g
