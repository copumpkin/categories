{-# OPTIONS --universe-polymorphism #-}
open import Level
open import Categories.Category
module Categories.Power.Functorial {o a : Level} (C : Category o a) where

open import Relation.Binary.PropositionalEquality using (proof-irrelevance)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∘_ to _∙_)
open import Relation.Binary using (module IsEquivalence)
open import Relation.Binary.HeterogeneousEquality as H using () renaming (_≅_ to _≣ʰ_; ≅-to-≡ to unhet)

open import Categories.Support.Irrelevance
open import Categories.Support.PropositionalEquality
open import Categories.Operations

import Categories.Power as Power
open Power C
open import Categories.Functor hiding (identityˡ) renaming (_≡_ to _≡F_; id to idF; promote to promoteF)
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation) renaming (promote to promoteNT)
open import Categories.Discrete
open import Categories.Equivalence.Strong hiding (module Equiv)

open Category using (Obj) renaming (_⇒_ to Hom)
open Category C using (_⇒_; Category-composes; _≡_; module Equiv)
open import Categories.FunctorCategory
open import Categories.Lift
open import Categories.NaturalIsomorphism as NI using (NaturalIsomorphism; module NaturalIsomorphism)
open Functor using () renaming (F₀ to map₀; F₁ to map₁)
open NaturalTransformation using (η)

z : Level
z = o ⊔ a

open import Categories.Categories using (Categories)
import Categories.Morphisms as M
open M (Categories z z) using (_≅_)

exp→functor₀ : ∀ {I} → Obj (Exp I) → Functor (Discrete I) C
exp→functor₀ X =
  record
  { F₀ = X
  ; F₁ = my-F₁
  ; identity = Equiv.refl
  ; homomorphism = λ {_ _ _ A≣B B≣C} → my-homomorphism A≣B B≣C
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

-- XXX can this just be done with refls?
exp→functorᵉ : ∀ {I} → EasyFunctor (Exp I) (Functorsᵉ (Discrete I) C)
exp→functorᵉ =
  record
  { F₀ = exp→functor₀
  ; F₁ = exp→functor₁
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  }

exp→functor : ∀ {I} → Functor (Exp I) (Functors (Discrete I) C)
exp→functor = EasyFunctor.functor exp→functorᵉ

functor→exp : ∀ {I} → Functor (Functors (Discrete I) C) (Exp I)
functor→exp =
  record
  { F₀ = Functor.F₀
  ; F₁ = NaturalTransformation.η
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  }

semicanonical : ∀ {I} → (F : Functor (Discrete I) C) → F ≡F (exp→functor₀ (map₀ F))
semicanonical {I} F ≣-refl = ≡⇒∼ F.identity
  where
  module F = Functor F
  open Heterogeneous C

canonical : ∀ {I} → (F : Functor (Discrete I) C) → F ≣ (exp→functor₀ (map₀ F))
canonical {I} F = promoteF F (exp→functor₀ (map₀ F)) (semicanonical F)

≣-subst₂-gone : ∀ {a b c d} {A : Set a} {B : Set b} (C : A → B → Set c) (D : A → B → Set d) (f : {x : A} {y : B} (z : C x y) → D x y) {x x′ : A} (x≣x′ : x ≣ x′) {y y′ : B} (y≣y′ : y ≣ y′) {z : C x y} → f (≣-subst₂ C x≣x′ y≣y′ z) ≣ʰ f z
≣-subst₂-gone C D f ≣-refl ≣-refl = H.refl

exp≋functor : ∀ {I} → StrongEquivalence (Exp I) (Functors (Discrete I) C)
exp≋functor {I} = record
  { F = exp→functor
  ; G = functor→exp
  ; weak-inverse = record
    { F∘G≅id = IsEquivalence.reflexive NI.equiv
                 (promoteF (exp→functor ∘ functor→exp) idF 
                   (λ {A B} f → sym (trans
                     (float₂-resp-∼ (canonical A) (canonical B))
                     (≡⇒∼ (promoteNT (float₂ (canonical A) (canonical B) f)
                                     (map₁ (exp→functor ∘ functor→exp) f)
                            (λ {x} → unhet
                              (≣-subst₂-gone (Hom FDIC) _ (λ g → η g x) (canonical A) (canonical B))))))))
    ; G∘F≅id = IsEquivalence.refl NI.equiv
    }
  }
  where
  FDIC = Functors (Discrete I) C
  module Sc (X : Obj FDIC) = NaturalIsomorphism (NI.≡→iso X (exp→functor₀ (map₀ X)) (semicanonical X))
  open Heterogeneous FDIC

exp≅functor : ∀ {I} → LiftC z z (Exp I) ≅ Functors (Discrete I) C
exp≅functor {I} =
  record
  { f = LiftFˡ exp→functor
  ; g = LiftFʳ functor→exp
  ; iso = record
    { isoˡ = ≣-refl
    ; isoʳ = promoteF f∘g idF (λ {A B} f → ir A B f)
    }
  }
  where
  FDIC = Functors (Discrete I) C
  f∘g = LiftFˡ exp→functor ∘ LiftFʳ functor→exp

  squash : ∀ (A : Obj FDIC) → Obj FDIC
  squash A = exp→functor₀ (map₀ A)

  ≣-cong′ : ∀ {a b} {A : Set a} {B : Set b} {x y : A} (f : (z : A) → (y ≣ z) → B) → (eq : x ≣ y) → f x (≣-sym eq) ≣ f y ≣-refl
  ≣-cong′ f ≣-refl = ≣-refl

  .squash-does-nothing : (A : Obj FDIC) → squash A ≣ A
  squash-does-nothing A = ≣-cong′ {B = Obj FDIC} (λ f eq → record {
                             F₀ = map₀ A;
                             F₁ = λ {i j : I} → f i j;
                             identity = λ {i} → ≣-subst (λ f → f i i ≣-refl ≡ C.id) eq (Functor.identity A {i});
                             homomorphism = λ {i j k i≣j j≣k} → ≣-subst (λ f → f i k (≣-trans i≣j j≣k) ≡ f j k j≣k ∘ f i j i≣j) eq (Functor.homomorphism A {f = i≣j} {j≣k})})
                    lemma₃
    where
    .lemma₁ : (i : I) (eq : i ≣ i) → map₁ A eq ≡ C.id
    lemma₁ i ≣-refl = ≣-trans (Functor.F-resp-≡ A ≣-refl) (Functor.identity A)

    .lemma₂ : (i j : I) (eq : i ≣ j) → map₁ (squash A) eq ≣ map₁ A eq
    lemma₂ i .i ≣-refl = ≣-sym (lemma₁ i ≣-refl)

    .lemma₃ : (λ (i j : I) → map₁ (squash A) {i} {j}) ≣ (λ (i j : I) → map₁ A {i} {j})
    lemma₃ = ≣-ext (λ (i : I) → ≣-ext (λ (j : I) → ≣-ext (lemma₂ i j)))

  ∼-subst : ∀ {o a} {C : Category o a} {A B A′ B′ : Obj C} (f : C [ A , B ]) (g : C [ A′ , B′ ]) (A′≣A : A′ ≣ A) (B′≣B : B′ ≣ B) → .(C [ ≣-subst (λ X → C [ X , B ]) A′≣A (≣-subst (λ Y → C [ A′ , Y ]) B′≣B g) ≡ f ]) → C [ g ∼ f ]
  ∼-subst {C = C} f g ≣-refl ≣-refl eq = ≡⇒∼ eq
    where open Heterogeneous C

  .∼-unsubst : ∀ {o a} {C : Category o a} {A B A′ B′ : Obj C} (f : C [ A , B ]) (g : C [ A′ , B′ ]) (A′≣A : A′ ≣ A) (B′≣B : B′ ≣ B) → C [ g ∼ f ] → C [ ≣-subst (λ X → C [ X , B ]) A′≣A (≣-subst (λ Y → C [ A′ , Y ]) B′≣B g) ≡ f ]
  ∼-unsubst f g ≣-refl ≣-refl (Heterogeneous.≡⇒∼ eq) = irr eq
    where open Heterogeneous C

  ≣-subst-irrel : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → (eq₁ eq₂ : x ≣ y) → ∀ {it} → ≣-subst P eq₁ it ≣ ≣-subst P eq₂ it
  ≣-subst-irrel _ ≣-refl ≣-refl = ≣-refl

  ≣-subst-cong : ∀ {a a′ p} {A : Set a} {A′ : Set a′} (P′ : A′ → Set p) (f : A → A′) {x y : A} (eq : x ≣ y) → ∀ {it} → ≣-subst (P′ ∙ f) eq it ≣ ≣-subst P′ (≣-cong f eq) it
  ≣-subst-cong P′ f ≣-refl = ≣-refl

  ≣-subst-fatten : ∀ {a a′ p} {A : Set a} {A′ : Set a′} (P′ : A′ → Set p) (f : A → A′) {x y : A} (eq : x ≣ y) (eq′ : f x ≣ f y) → ∀ {it} → ≣-subst (P′ ∙ f) eq it ≣ ≣-subst P′ eq′ it
  ≣-subst-fatten P′ f eq eq′ = ≣-trans (≣-subst-cong P′ f eq) (≣-subst-irrel P′ (≣-cong f eq) eq′)

  η-under-substˡ : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F F′ G : Functor C D} (α : NaturalTransformation F′ G) (F′≣F : F′ ≣ F) (c : Obj C) → η (≣-subst (λ H → NaturalTransformation H G) F′≣F α) c ≣ (≣-subst (λ (H : Functor C D) → D [ map₀ H c , map₀ G c ]) F′≣F (η α c))
  η-under-substˡ α ≣-refl c = ≣-refl

  η-under-substʳ : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G G′ : Functor C D} (α : NaturalTransformation F G′) (G′≣G : G′ ≣ G) (c : Obj C) → η (≣-subst (λ H → NaturalTransformation F H) G′≣G α) c ≣ (≣-subst (λ (H : Functor C D) → D [ map₀ F c , map₀ H c ]) G′≣G (η α c))
  η-under-substʳ α ≣-refl c = ≣-refl

  .lemma : (A B : Obj FDIC) (f : FDIC [ A , B ]) (i : I) (sqdn : ∀ X → squash X ≣ X) → C [ η (≣-subst (λ X → FDIC [ X , B ]) (sqdn A) (≣-subst (λ Y → FDIC [ squash A , Y ]) (sqdn B) (map₁ f∘g f))) i ≡ η f i ]
  lemma A B f i sqdn = C.Equiv.reflexive (
      begin
        η (≣-subst (λ X → FDIC [ X , B ]) (sqdn A) MESS) i
      ≣⟨ η-under-substˡ MESS (sqdn A) i ⟩
        ≣-subst (λ X → C [ loc X , loc B ]) (sqdn A) (η MESS i)
      ≣⟨ ≣-subst-fatten (λ c → C [ c , loc B ]) loc (sqdn A) ≣-refl ⟩
        η (≣-subst (λ Y → FDIC [ squash A , Y ]) (sqdn B) (map₁ f∘g f)) i
      ≣⟨ η-under-substʳ (map₁ f∘g f) (sqdn B) i ⟩
        ≣-subst (λ Y → C [ loc A , loc Y ]) (sqdn B) (η (map₁ f∘g f) i)
      ≣⟨ ≣-subst-fatten (λ c → C [ loc A , c ]) loc (sqdn B) ≣-refl ⟩
        η f i
      ∎)
    where
    open ≣-reasoning

    loc : Obj FDIC → Obj C
    loc X = map₀ X i

    MESS = ≣-subst (λ Y → FDIC [ squash A , Y ]) (sqdn B) (map₁ f∘g f)

  .ir : (A B : Obj FDIC) (f : FDIC [ A , B ]) → FDIC [ map₁ f∘g f ∼ f ]
  ir A B f = ∼-subst {C = FDIC} f (map₁ f∘g f) (squash-does-nothing A) (squash-does-nothing B) (promoteNT
    (≣-subst (λ X → FDIC [ X , B ]) (squash-does-nothing A) (≣-subst (λ Y → FDIC [ squash A , Y ]) (squash-does-nothing B) (map₁ f∘g f)))
    f
    (λ {x} → lemma A B f x squash-does-nothing))
