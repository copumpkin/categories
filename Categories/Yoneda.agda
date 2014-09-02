{-# OPTIONS --universe-polymorphism #-}
module Categories.Yoneda where

open import Level
open import Data.Product

open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning
open import Categories.Support.PropositionalEquality hiding (module ≣-reasoning)

open import Categories.Category
import Categories.Functor as Cat
open import Categories.Functor using (Functor; module Functor)
open import Categories.Functor.Hom
import Categories.Morphisms as Mor
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation) renaming (promote to promoteNT)
open import Categories.NaturalIsomorphism
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Presheaves
open import Categories.Agda

Embed : ∀ {o a} → (C : Category o a) → Functor C (Presheaves C)
Embed C = record
  { F₀ = λ x → Hom[ C ][-, x ]
  ; F₁ = λ {A B} → F₁ {A} {B}
  ; identity = promoteNT (F₁ id) idᴾ (≣-ext (λ _ → identityˡ))
  ; homomorphism = λ {_ _ _ f g} → promoteNT (F₁ (g ∘ f)) (F₁ g ∘ᴾ F₁ f) (≣-ext (λ _ → assoc))
  }
  where
  open Category C
  open Category (Presheaves C) using () renaming (_∘_ to _∘ᴾ_; id to idᴾ)
  open Equiv

  .commute′ : {A B X Y : Obj} (f : A ⇒ B) (g : Y ⇒ X) (x : X ⇒ A) → f ∘ id ∘ x ∘ g ≡ id ∘ (f ∘ x) ∘ g
  commute′ f g x = 
    begin
      f ∘ id ∘ x ∘ g
    ↑⟨ assoc ⟩
      (f ∘ id) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ˡ id-comm ⟩
      (id ∘ f) ∘ x ∘ g
    ≈⟨ assoc ⟩
      id ∘ f ∘ x ∘ g
    ↑⟨ ∘-resp-≡ʳ assoc ⟩
      id ∘ (f ∘ x) ∘ g
    ∎
    where open HomReasoning

  F₁ = λ {A B} f → record
    { η = λ X g → f ∘ g
    ; commute = λ g → ≣-ext (commute′ f g)
    }


module Embed {o a} C = Functor (Embed {o} {a} C)


Nat[Embed[_][c],F] : ∀ {o a} → (C : Category o a) -> Functor (Product (Presheaves C) (Category.op C)) (Sets _)
Nat[Embed[ C ][c],F] = Hom[ Presheaves C ][-,-] Cat.∘ ((Embed.op C Cat.∘ snd) ※ fst)
 where
   fst = πˡ {C = Presheaves C} {D = Category.op C}
   snd = πʳ {C = Presheaves C} {D = Category.op C}

F[c∈_] : ∀ {o a} → (C : Category o a) -> Functor (Product (Presheaves C) (Category.op C)) (Sets _)
F[c∈_] {o} {a} C = Lift-Sets (suc a ⊔ o) Cat.∘ eval {C = Category.op C} {D = Sets a}


yoneda : ∀ {o a} → (C : Category o a) -> NaturalIsomorphism Nat[Embed[ C ][c],F] F[c∈ C ]
yoneda C = record { F⇒G = F⇒G; F⇐G = F⇐G; iso = iso }
 where
  open NaturalTransformation
  open Categories.Functor.Functor
  module C = Category C
  open C.Equiv
  module M = Mor (Sets _)
  F⇒G : NaturalTransformation Nat[Embed[ C ][c],F] F[c∈ C ]
  F⇒G = record {
   η = λ {(F , c) → λ ε → lift (η ε c C.id)};
   commute = λ { {F , c₁} {G , c₂} (ε , f) {- {φ} {ψ} φ≡ψ -} →
     ≣-ext λ ψ → ≣-cong lift let open ≣-reasoning _ in begin
       η ε c₂ (η ψ c₂ (f C.∘ C.id))
     ↓⟨ ≣-cong (λ φ → η ε c₂ (η ψ c₂ φ)) C.id-comm ⟩
       η ε c₂ (η ψ c₂ (C.id C.∘ f))
     ↑⟨ ≣-cong (λ φ → η ε c₂ (η ψ c₂ φ)) C.identityˡ ⟩
       η ε c₂ (η ψ c₂ (C.id C.∘ C.id C.∘ f))
     ↓⟨ ≣-cong (η ε c₂) (≣-app (commute ψ _) _) ⟩
       η ε c₂ (F₁ F f (η ψ c₁ C.id))
     ↓⟨ ≣-app (commute ε _) _ ⟩
       F₁ G f (η ε c₁ (η ψ c₁ C.id))
     ∎ }}

  F⇐G : NaturalTransformation F[c∈ C ] Nat[Embed[ C ][c],F] 
  F⇐G = record {
   η = λ {(F , c) (lift Fc) →
                record { η = λ X f → F₁ F f Fc;
                         commute = λ {X} {Y} h → 
                           ≣-ext λ g → let open ≣-reasoning _ in
                           begin
                             F₁ F (C.id C.∘ g C.∘ h) Fc
                           ↓⟨ ≣-cong (λ f → F₁ F f Fc) C.identityˡ ⟩
                             F₁ F (g C.∘ h) Fc
                           ↓⟨ ≣-app (homomorphism F) _ ⟩
                             F₁ F h (F₁ F g Fc)
                           ∎
{-
                           let module s = Setoid (F₀ F Y)
                               module sr = SetoidReasoning (F₀ F Y)
                            in sr.begin
                               F₁ F (C.id C.∘ f C.∘ h) ⟨$⟩ lower Fc
                                 sr.↓⟨  F-resp-≡ F (trans C.identityˡ (C.∘-resp-≡ˡ f≡g)) (Setoid.refl (F₀ F c)) ⟩
                               F₁ F (g C.∘ h) ⟨$⟩ lower Fc 
                                 sr.↓⟨ homomorphism F (Setoid.refl (F₀ F c)) ⟩ 
                               F₁ F h ⟨$⟩ (F₁ F g ⟨$⟩ lower Fc) 
                                 sr.∎
-} }};
   commute = λ { {F , c₁} {G , c₂} (ε , e) → ≣-ext λ { (lift x) → promoteNT _ _ (λ {c} → ≣-ext λ f → let open ≣-reasoning _ in
     begin
       F₁ G f (F₁ G e (η ε c₁ x))
     ↑⟨ ≣-app (homomorphism G) _ ⟩
       F₁ G (e C.∘ f) (η ε c₁ x)
     ↑⟨ ≣-app (commute ε _) _ ⟩
       η ε c (F₁ F (e C.∘ f) x)
     ∎) } } }

  module F⇐G = NaturalTransformation F⇐G
  module F⇒G = NaturalTransformation F⇒G

  iso : (X : Category.Obj (Product (Presheaves C) C.op)) → M.Iso (F⇒G.η X) (F⇐G.η X)
  iso (F , c) = record {
    isoˡ = ≣-ext λ ψ → promoteNT _ _ λ {x} → ≣-ext λ f → let open ≣-reasoning _ in
      begin
        F₁ F f (η ψ c C.id)
      ↑⟨ ≣-app (commute ψ _) _ ⟩
        η ψ x (C.id C.∘ C.id C.∘ f)
      ↓⟨ ≣-cong (η ψ x) C.identityˡ ⟩
        η ψ x (C.id C.∘ f)
      ↓⟨ ≣-cong (η ψ x) C.identityˡ ⟩
        η ψ x f
      ∎;
    isoʳ = ≣-ext λ x → ≣-cong lift (≣-app (identity F) _) }


yoneda-iso : ∀ {o a} → (C : Category o a) (c d : Category.Obj C) -> 
               let open Mor (Sets _) in 
                  Functor.F₀ Hom[ Presheaves C ][ Embed.F₀ C c ,-] (Embed.F₀ C d) 
                ≅ Functor.F₀ (Lift-Sets (suc a ⊔ o)) (Functor.F₀ (Embed.F₀ C d) c) 
yoneda-iso C c d = record { f = ⇒.η X; g = ⇐.η X; 
                            iso = iso X } 
  where
    open NaturalIsomorphism (yoneda C)
    module iso F,c = Mor.Iso (Sets _) (iso F,c)
    X = ((Embed.F₀ C d) , c)


yoneda-inj : ∀ {o a} → (C : Category o a) (c d : Category.Obj C) -> NaturalIsomorphism (Embed.F₀ C c) (Embed.F₀ C d)
              -> Mor._≅_ C c d
yoneda-inj C c d ηiso = record { f = ⇒.η c C.id; g = ⇐.η d C.id; 
            iso = record { isoˡ = Lemma.lemma c d ηiso; 
                           isoʳ = Lemma.lemma d c (IsEquivalence.sym Categories.NaturalIsomorphism.equiv ηiso) 
                         } }
  where
    open import Relation.Binary
    module C = Category C
    open C.HomReasoning
    module Lemma (c d : C.Obj) (ηiso : NaturalIsomorphism (Embed.F₀ C c) (Embed.F₀ C d)) where
      open NaturalIsomorphism ηiso 
      module iso c = Mor.Iso _ (iso c)
      .lemma : (⇐.η d C.id) C.∘ (⇒.η c C.id) C.≡ C.id
      lemma = begin
                (⇐.η d C.id) C.∘ (⇒.η c C.id) 
              ↑⟨ C.identityˡ ⟩
                C.id C.∘ (⇐.η d C.id) C.∘ (⇒.η c C.id) 
              ↑⟨ ≣-app (⇐.commute (⇒.η c C.id)) _ ⟩ 
                ⇐.η c (C.id C.∘ C.id C.∘ (⇒.η c C.id)) 
              ↓⟨ ≣-cong (⇐.η c) (C.Equiv.trans C.identityˡ C.identityˡ) ⟩ 
                ⇐.η c (⇒.η c C.id)
              ↓⟨ ≣-app (iso.isoˡ c) _ ⟩ 
                C.id 
              ∎
    open NaturalIsomorphism ηiso