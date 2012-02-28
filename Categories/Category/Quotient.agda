{-# OPTIONS --universe-polymorphism #-}
module Categories.Category.Quotient where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive) renaming (_⇒_ to _⊆_)
open import Relation.Binary.HeterogeneousEquality as H using () renaming (_≅_ to _≋_; ≡-to-≅ to ≣-to-≋)
open import Function using (flip)

open import Categories.Support.Irrelevance
open import Categories.Support.PropositionalEquality hiding (module ≣-reasoning)
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning
open import Categories.Support.Quotients
open import Data.Product
open import Categories.Category

private
  ≋-ext : ∀ {a b} → H.Extensionality a b
  ≋-ext = H.≡-ext-to-≅-ext ≣-ext

record QCategory (o a e : Level) : Set (suc (o ⊔ a ⊔ e)) where 
  infixr 9 _∘_ _⊘ˡ_ _⊘_
  infix  4 _≡_

  field
    Obj : Set o
    _⇒_ : Rel Obj a
    _≡_ : ∀ {A B} → Rel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    .assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    .identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    .identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    equiv     : ∀ {A B} → IsEquivalence (_≡_ {A} {B})
    .∘-resp-≡  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

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

  private open Equiv

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

  _⇏_ = λ X Y → Quotient (X ⇒ Y) _≡_ equiv

  _⊘ˡ_ : ∀ {A B C} → (B ⇒ C) → (A ⇏ B) → (A ⇏ C)
  _⊘ˡ_ = λ g → qelim′ (λ f → ⌊ g ∘ f ⌉) (λ f≡f′ → qdiv (∘-resp-≡ʳ f≡f′))

  ⊘ˡ-compute : ∀ {A B C} {g : B ⇒ C} {f : A ⇒ B} → g ⊘ˡ ⌊ f ⌉ ≣ ⌊ g ∘ f ⌉
  ⊘ˡ-compute = qelim-compute′ (λ f≡f′ → qdiv (∘-resp-≡ʳ f≡f′))

  .⊘ˡ-coherent : ∀ {A B C} {g g′ : B ⇒ C} → g ≡ g′ → _⊘ˡ_ {A} g ≣ _⊘ˡ_ g′
  ⊘ˡ-coherent {A} {B} {C} {g} {g′} g≡g′ = ≣-ext (qequate′
    (λ f → let open ≣-reasoning (A ⇏ C) in 
      begin
        g ⊘ˡ ⌊ f ⌉
      ↓⟨ ⊘ˡ-compute ⟩
        ⌊ g ∘ f ⌉
      ↓⟨ qdiv (∘-resp-≡ˡ g≡g′) ⟩
        ⌊ g′ ∘ f ⌉
      ↑⟨ ⊘ˡ-compute ⟩
        g′ ⊘ˡ ⌊ f ⌉
      ∎))

  _⊘_ : ∀ {A B C} → (B ⇏ C) → (A ⇏ B) → (A ⇏ C)
  _⊘_ {A} {B} {C} = qelim′ _⊘ˡ_ ⊘ˡ-coherent

  ⊘-compute : ∀ {A B C} {g : B ⇒ C} → _⊘_ {A} ⌊ g ⌉ ≣ _⊘ˡ_ g
  ⊘-compute = qelim-compute′ ⊘ˡ-coherent

  ⊘-computeˡ : ∀ {A B C} {g : B ⇒ C} {f : A ⇏ B} → ⌊ g ⌉ ⊘ f ≣ g ⊘ˡ f
  ⊘-computeˡ {f = f} = ≣-cong (λ F → F f) ⊘-compute

  ⊘-compute₂ : ∀ {A B C} {g : B ⇒ C} {f : A ⇒ B} → ⌊ g ⌉ ⊘ ⌊ f ⌉ ≣ ⌊ g ∘ f ⌉
  ⊘-compute₂ = ≣-trans ⊘-computeˡ ⊘ˡ-compute

  assoc₃ : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D)
         → (⌊ h ⌉ ⊘ ⌊ g ⌉) ⊘ ⌊ f ⌉ ≣ ⌊ h ⌉ ⊘ (⌊ g ⌉ ⊘ ⌊ f ⌉)
  assoc₃ f g h = 
    begin
      (⌊ h ⌉ ⊘ ⌊ g ⌉) ⊘ ⌊ f ⌉
    ↓⟨ ≣-cong (λ v → v ⊘ ⌊ f ⌉) ⊘-compute₂ ⟩
      ⌊ h ∘ g ⌉ ⊘ ⌊ f ⌉
    ↓⟨ ⊘-compute₂ ⟩
      ⌊ (h ∘ g) ∘ f ⌉
    ↓⟨ qdiv assoc ⟩
      ⌊ h ∘ (g ∘ f) ⌉
    ↑⟨ ⊘-compute₂ ⟩
      ⌊ h ⌉ ⊘ ⌊ g ∘ f ⌉
    ↑⟨ ≣-cong (_⊘_ ⌊ h ⌉) ⊘-compute₂ ⟩
      ⌊ h ⌉ ⊘ (⌊ g ⌉ ⊘ ⌊ f ⌉)
    ∎
    where open ≣-reasoning _

  assoc₂ : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇏ D)
           → (h ⊘ ⌊ g ⌉) ⊘ ⌊ f ⌉ ≣ h ⊘ (⌊ g ⌉ ⊘ ⌊ f ⌉)
  assoc₂ f g = qequate′ (assoc₃ f g)

  -- assoc₂-compute : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D)
  --                  → assoc₂ f g ⌊ h ⌉ ≣ assoc₃ f g h
  -- assoc₂-compute f g h = qelim-compute {P = λ k → (k ⊘ ⌊ g ⌉) ⊘ ⌊ f ⌉ ≣ k ⊘ (⌊ g ⌉ ⊘ ⌊ f ⌉)} (qequate′-coherent (λ k → (k ⊘ ⌊ g ⌉) ⊘ ⌊ f ⌉) (λ k → k ⊘ (⌊ g ⌉ ⊘ ⌊ f ⌉)) (assoc₃ f g))

  assoc₂-coherent : ∀ {A B C D} (f : A ⇒ B) {g g′ : B ⇒ C} → g ≡ g′ → assoc₂ {D = D} f g ≋ assoc₂ f g′
  assoc₂-coherent {A} {B} {C} {D} f {g} {g′} g≡g′ = ≋-ext
    (λ h → ≣-cong (λ ⌊g⌉ → (h ⊘ ⌊g⌉) ⊘ ⌊ f ⌉ ≣ h ⊘ (⌊g⌉ ⊘ ⌊ f ⌉)) (qdiv g≡g′))
    (qequate {f = assoc₂ f g} {g = assoc₂ f g′} (λ h → qequate′-coherent
      (λ ⌊g⌉ → (⌊ h ⌉ ⊘ ⌊g⌉) ⊘ ⌊ f ⌉)
      (λ ⌊g⌉ → ⌊ h ⌉ ⊘ (⌊g⌉ ⊘ ⌊ f ⌉))
      (λ j → assoc₂ f j ⌊ h ⌉)
      g≡g′))

  assoc₁ : ∀ {A B C D} (f : A ⇒ B) (g : B ⇏ C) (h : C ⇏ D)
         → (h ⊘ g) ⊘ ⌊ f ⌉ ≣ h ⊘ (g ⊘ ⌊ f ⌉)
  assoc₁ f = qelim (assoc₂ f) (assoc₂-coherent f)

  -- assoc₁-compute : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C)
  --                  → assoc₁ {D = D} f ⌊ g ⌉ ≣ assoc₂ {D = D} f g
  -- assoc₁-compute {C = C} {D} f g = qelim-compute {P = λ j → ∀ (h : C ⇏ D) → (h ⊘ j) ⊘ ⌊ f ⌉ ≣ h ⊘ (j ⊘ ⌊ f ⌉)} (assoc₂-coherent f)

  assoc₁-coherent : ∀ {A B C D} {f f′ : A ⇒ B} → f ≡ f′ → assoc₁ {C = C} {D} f ≋ assoc₁ {C = C} {D} f′
  assoc₁-coherent {A} {B} {C} {D} {f} {f′} f≡f′ = ≋-ext
    (λ g → ≣-cong (λ ⌊f⌉ → ∀ (h : C ⇏ D) → (h ⊘ g) ⊘ ⌊f⌉ ≣ h ⊘ (g ⊘ ⌊f⌉)) (qdiv f≡f′))
    (qequate {f = assoc₁ f} {g = assoc₁ f′} (λ g → ≋-ext
      (λ h → ≣-cong (λ ⌊f⌉ → (h ⊘ ⌊ g ⌉) ⊘ ⌊f⌉ ≣ h ⊘ (⌊ g ⌉ ⊘ ⌊f⌉)) (qdiv f≡f′))
      (λ h → qequate′-coherent (λ ⌊f⌉ → (h ⊘ ⌊ g ⌉) ⊘ ⌊f⌉)
                               (λ ⌊f⌉ → h ⊘ (⌊ g ⌉ ⊘ ⌊f⌉))
                               (λ i → assoc₁ i ⌊ g ⌉ h)
                               f≡f′)))

  category : Category o (a ⊔ e)
  category = record 
    { Obj = Obj
    ; _⇒_ = _⇏_
    ; _∘_ = _⊘_
    ; id = ⌊ id ⌉
    ; ASSOC = qelim
      assoc₁
      assoc₁-coherent
    ; IDENTITYˡ = qequate′ (λ f → ≣-trans ⊘-compute₂ (qdiv identityˡ))
    ; IDENTITYʳ = qequate′ (λ f → ≣-trans ⊘-compute₂ (qdiv identityʳ))
    }

  CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare f g h i = h ∘ f ≡ i ∘ g


  .id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≡ g) → f ≡ id
  id-unique g∘f≡g = trans (sym identityˡ) (g∘f≡g id)

  .id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ id ∘ f
  id-comm = trans identityʳ (sym identityˡ)

_[[_,_]] : ∀ {o a e} → (C : QCategory o a e) → (X : QCategory.Obj C) → (Y : QCategory.Obj C) → Set a
_[[_,_]] = QCategory._⇒_

_[[_≡_]] : ∀ {o a e} → (C : QCategory o a e) → ∀ {X Y} (f g : C [[ X , Y ]]) → Set e
_[[_≡_]] = QCategory._≡_

_[[_∘_]] : ∀ {o a e} → (C : QCategory o a e) → ∀ {X Y Z} (f : C [[ Y , Z ]]) → (g : C [[ X , Y ]]) → C [[ X , Z ]]
_[[_∘_]] = QCategory._∘_

-- Should this live in the Category record itself? It doesn't seem terribly useful for most situations
module QHeterogeneous {o a e} (C : QCategory o a e) where
  open QCategory C
  open Equiv renaming (refl to refl′; sym to sym′; trans to trans′; reflexive to reflexive′)

  data _∼_ {A B} (f : A ⇒ B) : ∀ {X Y} → (X ⇒ Y) → Set (a ⊔ e) where
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

  float₂-resp-∼ : ∀ {A A′ B B′} (A≣A′ : A ≣ A′) (B≣B′ : B ≣ B′) {f : C [[ A , B ]]} → f ∼ float₂ A≣A′ B≣B′ f
  float₂-resp-∼ ≣-refl ≣-refl = refl

  floatˡ-resp-∼ : ∀ {A B B′} (B≣B′ : B ≣ B′) {f : C [[ A , B ]]} → f ∼ floatˡ B≣B′ f
  floatˡ-resp-∼ ≣-refl = refl

  floatʳ-resp-∼ : ∀ {A A′ B} (A≣A′ : A ≣ A′) {f : C [[ A , B ]]} → f ∼ floatʳ A≣A′ f
  floatʳ-resp-∼ ≣-refl = refl
  
_[[_∼_]] : ∀ {o a e} (C : QCategory o a e) {A B} (f : C [[ A , B ]]) {X Y} (g : C [[ X , Y ]]) → Set (a ⊔ e)
C [[ f ∼ g ]] = QHeterogeneous._∼_ C f g