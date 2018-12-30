{-# OPTIONS --universe-polymorphism #-}
open import Level
open import Categories.Category
module Categories.Power.Functorial {o ℓ e : Level} (C : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality using (≡-irrelevance)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∘_ to _∙_)
open import Relation.Binary using (module IsEquivalence)

open import Categories.Support.PropositionalEquality
import Categories.Power as Power
open Power C
open import Categories.Functor hiding (identityˡ) renaming (_≡_ to _≡F_; _∘_ to _∘F_; id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation)
open import Categories.Discrete
open import Categories.Equivalence.Strong hiding (module Equiv)

open Category using (Obj)
open Category C using (_⇒_; _∘_; _≡_; module Equiv)
open import Categories.FunctorCategory
open import Categories.Lift
open import Categories.NaturalIsomorphism as NI using (NaturalIsomorphism; module NaturalIsomorphism)
open Functor using () renaming (F₀ to map₀; F₁ to map₁)
open NaturalTransformation using (η)

z : Level
z = o ⊔ ℓ ⊔ e

open import Categories.Categories using (Categories)
import Categories.Morphisms as M
open M (Categories z z e) using (_≅_)

exp→functor₀ : ∀ {I} → Obj (Exp I) → Functor (Discrete I) C
exp→functor₀ X =
  record
  { F₀ = X
  ; F₁ = my-F₁
  ; identity = Equiv.refl
  ; homomorphism = λ {_ _ _ A≣B B≣C} → my-homomorphism A≣B B≣C
  ; F-resp-≡ = λ {_ _ e1 e2} _ → Equiv.reflexive (≣-cong my-F₁ (≡-irrelevance e1 e2))
  }
  where
  my-F₁ : ∀ {A B} → (A ≣ B) → (X A ⇒ X B)
  my-F₁ ≣-refl = C.id
  .my-homomorphism : ∀ {A B C} (A≣B : A ≣ B) (B≣C : B ≣ C) → my-F₁ (≣-trans A≣B B≣C) ≡ my-F₁ B≣C ∘ my-F₁ A≣B
  my-homomorphism ≣-refl ≣-refl = Equiv.sym C.identityˡ

exp→functor₁ : ∀ {I} {X Y} → Exp I [ X , Y ] → NaturalTransformation (exp→functor₀ X) (exp→functor₀ Y)
exp→functor₁ {X = X} {Y} F = record { η = F; commute = my-commute }
  where
  .my-commute : ∀ {A B} (A≣B : A ≣ B) → F B ∘ map₁ (exp→functor₀ X) A≣B ≡ map₁ (exp→functor₀ Y) A≣B ∘ F A
  my-commute ≣-refl = Equiv.trans C.identityʳ (Equiv.sym C.identityˡ)

exp→functor : ∀ {I} → Functor (Exp I) (Functors (Discrete I) C)
exp→functor =
  record
  { F₀ = exp→functor₀
  ; F₁ = exp→functor₁
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≡ = λ eqs {x} → eqs x
  }

functor→exp : ∀ {I} → Functor (Functors (Discrete I) C) (Exp I)
functor→exp =
  record
  { F₀ = Functor.F₀
  ; F₁ = NaturalTransformation.η
  ; identity = λ _ → Equiv.refl
  ; homomorphism = λ _ → Equiv.refl
  ; F-resp-≡ = λ eqs i → eqs {i}
  }

semicanonical : ∀ {I} → (F : Functor (Discrete I) C) → F ≡F (exp→functor₀ (map₀ F))
semicanonical {I} F ≣-refl = ≡⇒∼ F.identity
  where
  module F = Functor F
  open Heterogeneous C

exp≋functor : ∀ {I} → StrongEquivalence (Exp I) (Functors (Discrete I) C)
exp≋functor {I} = record
  { F = exp→functor
  ; G = functor→exp
  ; weak-inverse = record
    { F∘G≅id = record
      { F⇒G = record
        { η = Sc.F⇐G
        ; commute = λ f → Equiv.trans C.identityˡ (Equiv.sym C.identityʳ)
        }
      ; F⇐G = record
        { η = Sc.F⇒G
        ; commute = λ f → Equiv.trans C.identityˡ (Equiv.sym C.identityʳ)
        }
      ; iso = λ X → record { isoˡ = C.identityˡ; isoʳ = C.identityˡ }
      }
    ; G∘F≅id = IsEquivalence.refl NI.equiv
    }
  }
  where
  FDIC = Functors (Discrete I) C
  module Sc (X : Obj FDIC) = NaturalIsomorphism (NI.≡→iso X (exp→functor₀ (map₀ X)) (semicanonical X))

exp≅functor : (ext : ∀ {a b} {A : Set a} {B : A → Set b} (f g : (x : A) → B x) → (∀ x → f x ≣ g x) → f ≣ g) → (id-propositionally-unique : (A : C.Obj) (f : A ⇒ A) → .(f ≡ C.id) → f ≣ C.id) → ∀ {I} → LiftC z z e (Exp I) ≅ Functors (Discrete I) C
exp≅functor ext id-propositionally-unique {I} =
  record
  { f = LiftFˡ exp→functor
  ; g = LiftFʳ functor→exp
  ; iso = record
    { isoˡ = λ f → Heterogeneous.refl _
    ; isoʳ = λ {A B} f → ir A B f
    }
  }
  where
  FDIC = Functors (Discrete I) C
  f∘g = LiftFˡ exp→functor ∘F LiftFʳ functor→exp

  squash : ∀ (A : Obj FDIC) → Obj FDIC
  squash A = exp→functor₀ (map₀ A)

  ≣-cong′ : ∀ {a b} {A : Set a} {B : Set b} {x y : A} (f : (z : A) → (y ≣ z) → B) → (eq : x ≣ y) → f x (≣-sym eq) ≣ f y ≣-refl
  ≣-cong′ f ≣-refl = ≣-refl

  squash-does-nothing : (A : Obj FDIC) → squash A ≣ A
  squash-does-nothing A = ≣-cong′ {B = Obj FDIC} (λ f eq → record {
                             F₀ = map₀ A;
                             F₁ = λ {i j : I} → f i j;
                             identity = λ {i} → ≣-subst (λ f → f i i ≣-refl ≡ C.id) eq (Functor.identity A {i});
                             homomorphism = λ {i j k i≣j j≣k} → ≣-subst (λ f → f i k (≣-trans i≣j j≣k) ≡ f j k j≣k ∘ f i j i≣j) eq (Functor.homomorphism A {f = i≣j} {j≣k});
                             F-resp-≡ = λ {i j ij ji} → ≣-subst (λ f → ⊤ → f i j ij ≡ f i j ji) eq (Functor.F-resp-≡ A {i} {j} {ij} {ji}) })
                    lemma₃
    where
    .lemma₁ : (i : I) (eq : i ≣ i) → map₁ A eq ≡ C.id
    lemma₁ i eq = Equiv.trans (Functor.F-resp-≡ A tt) (Functor.identity A)

    lemma₂ : (i j : I) (eq : i ≣ j) → map₁ (squash A) eq ≣ map₁ A eq
    lemma₂ i .i ≣-refl = ≣-sym (id-propositionally-unique (map₀ A i) (map₁ A ≣-refl) (lemma₁ i ≣-refl))

    lemma₃ : (λ (i j : I) → map₁ (squash A) {i} {j}) ≣ (λ (i j : I) → map₁ A {i} {j})
    lemma₃ = ext (λ (i j : I) → map₁ (squash A)) (λ (i j : I) → map₁ A)
      (λ (i : I) → ext (λ (j : I) → map₁ (squash A)) (λ (j : I) → map₁ A)
        (λ (j : I) → ext (map₁ (squash A)) (map₁ A) (lemma₂ i j)))

  ∼-subst : ∀ {o ℓ e} {C : Category o ℓ e} {A B A′ B′ : Obj C} (f : C [ A , B ]) (g : C [ A′ , B′ ]) (A′≣A : A′ ≣ A) (B′≣B : B′ ≣ B) → .(C [ ≣-subst (λ X → C [ X , B ]) A′≣A (≣-subst (λ Y → C [ A′ , Y ]) B′≣B g) ≡ f ]) → C [ g ∼ f ]
  ∼-subst {C = C} f g ≣-refl ≣-refl eq = ≡⇒∼ eq
    where open Heterogeneous C

  .∼-unsubst : ∀ {o ℓ e} {C : Category o ℓ e} {A B A′ B′ : Obj C} (f : C [ A , B ]) (g : C [ A′ , B′ ]) (A′≣A : A′ ≣ A) (B′≣B : B′ ≣ B) → C [ g ∼ f ] → C [ ≣-subst (λ X → C [ X , B ]) A′≣A (≣-subst (λ Y → C [ A′ , Y ]) B′≣B g) ≡ f ]
  ∼-unsubst f g ≣-refl ≣-refl (Heterogeneous.≡⇒∼ eq) = irr eq
    where open Heterogeneous C

  ≣-subst-irrel : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → (eq₁ eq₂ : x ≣ y) → ∀ {it} → ≣-subst P eq₁ it ≣ ≣-subst P eq₂ it
  ≣-subst-irrel _ ≣-refl ≣-refl = ≣-refl

  ≣-subst-cong : ∀ {a a′ p} {A : Set a} {A′ : Set a′} (P′ : A′ → Set p) (f : A → A′) {x y : A} (eq : x ≣ y) → ∀ {it} → ≣-subst (P′ ∙ f) eq it ≣ ≣-subst P′ (≣-cong f eq) it
  ≣-subst-cong P′ f ≣-refl = ≣-refl

  ≣-subst-fatten : ∀ {a a′ p} {A : Set a} {A′ : Set a′} (P′ : A′ → Set p) (f : A → A′) {x y : A} (eq : x ≣ y) (eq′ : f x ≣ f y) → ∀ {it} → ≣-subst (P′ ∙ f) eq it ≣ ≣-subst P′ eq′ it
  ≣-subst-fatten P′ f eq eq′ = ≣-trans (≣-subst-cong P′ f eq) (≣-subst-irrel P′ (≣-cong f eq) eq′)

  η-under-substˡ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F F′ G : Functor C D} (α : NaturalTransformation F′ G) (F′≣F : F′ ≣ F) (c : Obj C) → η (≣-subst (λ H → NaturalTransformation H G) F′≣F α) c ≣ (≣-subst (λ (H : Functor C D) → D [ map₀ H c , map₀ G c ]) F′≣F (η α c))
  η-under-substˡ α ≣-refl c = ≣-refl

  η-under-substʳ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G G′ : Functor C D} (α : NaturalTransformation F G′) (G′≣G : G′ ≣ G) (c : Obj C) → η (≣-subst (λ H → NaturalTransformation F H) G′≣G α) c ≣ (≣-subst (λ (H : Functor C D) → D [ map₀ F c , map₀ H c ]) G′≣G (η α c))
  η-under-substʳ α ≣-refl c = ≣-refl

  .lemma : (A B : Obj FDIC) (f : FDIC [ A , B ]) (i : I) → C [ η (≣-subst (λ X → FDIC [ X , B ]) (squash-does-nothing A) (≣-subst (λ Y → FDIC [ squash A , Y ]) (squash-does-nothing B) (map₁ f∘g f))) i ≡ η f i ]
  lemma A B f i =
    let loc X = map₀ X i in
    let sqdnA = squash-does-nothing A in
    let sqdnB = squash-does-nothing B in
    let MESS = ≣-subst (λ Y → FDIC [ squash A , Y ]) sqdnB (map₁ f∘g f) in

    C.Equiv.reflexive (
      begin
        η (≣-subst (λ X → FDIC [ X , B ]) sqdnA MESS) i
      ≣⟨ η-under-substˡ MESS sqdnA i ⟩
        ≣-subst (λ X → C [ loc X , loc B ]) sqdnA (η MESS i)
      ≣⟨ ≣-subst-fatten (λ c → C [ c , loc B ]) loc sqdnA ≣-refl ⟩
        η (≣-subst (λ Y → FDIC [ squash A , Y ]) sqdnB (map₁ f∘g f)) i
      ≣⟨ η-under-substʳ (map₁ f∘g f) sqdnB i ⟩
        ≣-subst (λ Y → C [ loc A , loc Y ]) sqdnB (η (map₁ f∘g f) i)
      ≣⟨ ≣-subst-fatten (λ c → C [ loc A , c ]) loc sqdnB ≣-refl ⟩
        η f i
      ∎)
    where
    open ≣-reasoning

  ir : (A B : Obj FDIC) (f : FDIC [ A , B ]) → FDIC [ map₁ f∘g f ∼ f ]
  ir A B f = ∼-subst {C = FDIC} f (map₁ f∘g f) (squash-does-nothing A) (squash-does-nothing B) (λ {x} → lemma A B f x)
