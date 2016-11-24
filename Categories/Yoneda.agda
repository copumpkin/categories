{-# OPTIONS --universe-polymorphism #-}
module Categories.Yoneda where

open import Level
open import Data.Product

open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning

open import Categories.Category
import Categories.Functor as Cat
open import Categories.Functor using (Functor; module Functor)
open import Categories.Functor.Hom
import Categories.Morphisms as Mor
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation)
open import Categories.NaturalIsomorphism
open import Categories.Product
open import Categories.FunctorCategory
open import Categories.Presheaves
open import Categories.Agda

Embed : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Presheaves C)
Embed C = record
  { F₀ = λ x → Hom[ C ][-, x ]
  ; F₁ = λ f → record 
    { η = λ X → record 
      { _⟨$⟩_ = λ g → f ∘ g
      ; cong = λ x → ∘-resp-≡ʳ x
      }
    ; commute = commute′ f
    }
  ; identity = λ x≡y → trans identityˡ x≡y
  ; homomorphism = λ x≡y → trans (∘-resp-≡ʳ x≡y) assoc
  ; F-resp-≡ = λ f≡g h≡i → ∘-resp-≡ f≡g h≡i
  }
  where
  open Category C
  open Equiv

  .commute′ : {A B X Y : Obj} (f : A ⇒ B) (g : Y ⇒ X) {x y : X ⇒ A} → x ≡ y → f ∘ id ∘ x ∘ g ≡ id ∘ (f ∘ y) ∘ g
  commute′ f g {x} {y} x≡y = 
    begin
      f ∘ id ∘ x ∘ g
    ↑⟨ assoc ⟩
      (f ∘ id) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ˡ id-comm ⟩
      (id ∘ f) ∘ x ∘ g
    ≈⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ x≡y) ⟩
      (id ∘ f) ∘ y ∘ g
    ≈⟨ assoc ⟩
      id ∘ f ∘ y ∘ g
    ↑⟨ ∘-resp-≡ʳ assoc ⟩
      id ∘ (f ∘ y) ∘ g
    ∎
    where open HomReasoning

module Embed {o ℓ e} C = Functor (Embed {o} {ℓ} {e} C)


Nat[Embed[_][c],F] : ∀ {o ℓ e} → (C : Category o ℓ e) -> Functor (Product (Presheaves C) (Category.op C)) (ISetoids _ _)
Nat[Embed[ C ][c],F] = Hom[ Presheaves C ][-,-] Cat.∘ ((Embed.op C Cat.∘ snd) ※ fst)
 where
   fst = πˡ {C = Presheaves C} {D = Category.op C}
   snd = πʳ {C = Presheaves C} {D = Category.op C}

F[c∈_] : ∀ {o ℓ e} → (C : Category o ℓ e) -> Functor (Product (Presheaves C) (Category.op C)) (ISetoids _ _)
F[c∈_] {o} {ℓ} {e} C = Lift-IS (suc e ⊔ suc ℓ ⊔ o) (o ⊔ ℓ) Cat.∘ eval {C = Category.op C} {D = ISetoids ℓ e}


yoneda : ∀ {o ℓ e} → (C : Category o ℓ e) -> NaturalIsomorphism Nat[Embed[ C ][c],F] F[c∈ C ]
yoneda C = record { F⇒G = F⇒G; F⇐G = F⇐G; iso = iso }
 where
  open NaturalTransformation
  open Categories.Functor.Functor
  open import Categories.Support.SetoidFunctions
  module C = Category C
  open C.Equiv
  module M = Mor (ISetoids _ _)
  F⇒G : NaturalTransformation Nat[Embed[ C ][c],F] F[c∈ C ]
  F⇒G = record {
   η = λ {(F , c) → 
          record { _⟨$⟩_ = λ ε → lift (η ε c ⟨$⟩ C.id);
                   cong  = λ x → lift (x refl) }};
   commute = λ { {F , c₁} {G , c₂} (ε , f) {φ} {ψ} φ≡ψ → lift
     (let module s = Setoid (F₀ G c₂)
          module sr = SetoidReasoning (F₀ G c₂)
          module t = Setoid (F₀ F c₂)
          module tr = SetoidReasoning (F₀ F c₂)
       in s.sym (sr.begin 
       F₁ G f ⟨$⟩ (η ε c₁ ⟨$⟩ (η ψ c₁ ⟨$⟩ C.id))                     
         sr.↑⟨ commute ε f (Setoid.refl (F₀ F c₁)) ⟩
       η ε c₂ ⟨$⟩ (F₁ F f ⟨$⟩ (η ψ c₁ ⟨$⟩ C.id))                      
         sr.↓⟨ cong (η ε c₂) (tr.begin
               F₁ F f ⟨$⟩ (η ψ c₁ ⟨$⟩ C.id) 
                 tr.↑⟨ commute ψ f (refl {x = C.id}) ⟩
               η ψ c₂ ⟨$⟩ C.id C.∘ C.id C.∘ f 
                 tr.↑⟨ φ≡ψ (trans C.identityʳ (trans (sym C.identityˡ) (sym C.identityˡ))) ⟩
               η φ c₂ ⟨$⟩ f C.∘ C.id 
                 tr.∎) ⟩
       η ε c₂ ⟨$⟩ (η φ c₂ ⟨$⟩ f C.∘ C.id) sr.∎  )) }}

  F⇐G : NaturalTransformation F[c∈ C ] Nat[Embed[ C ][c],F] 
  F⇐G = record {
   η = λ {(F , c) →
     record { _⟨$⟩_ = λ Fc →
                record { η = λ X →
                           record { _⟨$⟩_ = λ f → F₁ F f ⟨$⟩ lower Fc;
                                    cong  = λ eq → F-resp-≡ F eq (Setoid.refl (F₀ F c)) };
                         commute = λ {X} {Y} h {f} {g} f≡g →
                           let module s = Setoid (F₀ F Y)
                               module sr = SetoidReasoning (F₀ F Y)
                            in sr.begin
                               F₁ F (C.id C.∘ f C.∘ h) ⟨$⟩ lower Fc
                                 sr.↓⟨  F-resp-≡ F (trans C.identityˡ (C.∘-resp-≡ˡ f≡g)) (Setoid.refl (F₀ F c)) ⟩
                               F₁ F (g C.∘ h) ⟨$⟩ lower Fc 
                                 sr.↓⟨ homomorphism F (Setoid.refl (F₀ F c)) ⟩ 
                               F₁ F h ⟨$⟩ (F₁ F g ⟨$⟩ lower Fc) 
                                 sr.∎ };
              cong  = λ i≡j {X} {f} {g} f≡g → F-resp-≡ F f≡g (lower i≡j) }};
   commute = λ { {F , c₁} {G , c₂} (ε , e) {lift i} {lift j} i≡j {X} {f} {g} f≡g → 
     let module s = Setoid (F₀ G X)
         module sr = SetoidReasoning (F₀ G X)
      in sr.begin
         F₁ G f ⟨$⟩ (F₁ G e ⟨$⟩ (η ε c₁ ⟨$⟩ i)) 
           sr.↑⟨ homomorphism G {f = e} {g = f} (Setoid.refl (F₀ G c₁)) ⟩
         F₁ G (e C.∘ f) ⟨$⟩ (η ε c₁ ⟨$⟩ i)
           sr.↑⟨ commute ε (e C.∘ f) (Setoid.refl (F₀ F c₁)) ⟩
         η ε X ⟨$⟩ (F₁ F (e C.∘ f) ⟨$⟩ i) 
           sr.↓⟨ cong (η ε X) (F-resp-≡ F (C.∘-resp-≡ʳ f≡g) (lower i≡j)) ⟩
         η ε X ⟨$⟩ (F₁ F (e C.∘ g) ⟨$⟩ j) 
           sr.∎}} 

  module F⇐G = NaturalTransformation F⇐G
  module F⇒G = NaturalTransformation F⇒G

  iso : (X : Category.Obj (Product (Presheaves C) C.op)) → M.Iso (F⇒G.η X) (F⇐G.η X)
  iso (F , c) = record {
    isoˡ = λ { {ε₁} {ε₂} ε₁≡ε₂ {X} {f} {g} f≡g → 
      let module s = Setoid (F₀ F X)
          open SetoidReasoning (F₀ F X)
       in begin 
           F₁ F f ⟨$⟩ (η ε₁ c ⟨$⟩ C.id)
             ↑⟨ commute ε₁ f {C.id} {C.id} refl ⟩
           η ε₁ X ⟨$⟩ C.id C.∘ C.id C.∘ f
             ↓⟨ ε₁≡ε₂ (trans C.identityˡ (trans C.identityˡ f≡g)) ⟩
           η ε₂ X ⟨$⟩ g
             ∎ };
    isoʳ = λ eq → lift (identity F (lower eq)) }

yoneda-iso : ∀ {o ℓ e} → (C : Category o ℓ e) (c d : Category.Obj C) -> 
               let open Mor (ISetoids _ _) in 
                  Functor.F₀ Hom[ Presheaves C ][ Embed.F₀ C c ,-] (Embed.F₀ C d) 
                ≅ Functor.F₀ (Lift-IS (suc e ⊔ suc ℓ ⊔ o) (o ⊔ ℓ)) (Functor.F₀ (Embed.F₀ C d) c) 
yoneda-iso C c d = record { f = ⇒.η X; g = ⇐.η X; 
                            iso = iso X } 
  where
    open NaturalIsomorphism (yoneda C)
    module iso F,c = Mor.Iso (iso F,c)
    X = ((Embed.F₀ C d) , c)


yoneda-inj : ∀ {o ℓ e} → (C : Category o ℓ e) (c d : Category.Obj C) -> NaturalIsomorphism (Embed.F₀ C c) (Embed.F₀ C d)
              -> Mor._≅_ C c d
yoneda-inj C c d ηiso = record { f = ⇒.η c ⟨$⟩ C.id; g = ⇐.η d ⟨$⟩ C.id; 
            iso = record { isoˡ = Lemma.lemma c d ηiso; 
                           isoʳ = Lemma.lemma d c (IsEquivalence.sym Categories.NaturalIsomorphism.equiv ηiso) 
                         } }
  where
    open import Categories.Support.SetoidFunctions
    open import Relation.Binary
    module C = Category C
    open C.HomReasoning
    module Lemma (c d : C.Obj) (ηiso : NaturalIsomorphism (Embed.F₀ C c) (Embed.F₀ C d)) where
      open NaturalIsomorphism ηiso 
      module iso c = Mor.Iso (iso c)
      .lemma : (⇐.η d ⟨$⟩ C.id) C.∘ (⇒.η c ⟨$⟩ C.id) C.≡ C.id
      lemma = begin
                (⇐.η d ⟨$⟩ C.id) C.∘ (⇒.η c ⟨$⟩ C.id) 
              ↑⟨ C.identityˡ ⟩
                C.id C.∘ (⇐.η d ⟨$⟩ C.id) C.∘ (⇒.η c ⟨$⟩ C.id) 
              ↑⟨ ⇐.commute (⇒.η c ⟨$⟩ C.id) {C.id} C.Equiv.refl ⟩ 
                ⇐.η c ⟨$⟩ C.id C.∘ C.id C.∘ (⇒.η c ⟨$⟩ C.id) 
              ↓⟨ cong (⇐.η c) (C.Equiv.trans C.identityˡ C.identityˡ) ⟩ 
                ⇐.η c ⟨$⟩ (⇒.η c ⟨$⟩ C.id)
              ↓⟨ iso.isoˡ c C.Equiv.refl ⟩ 
                C.id 
              ∎
    open NaturalIsomorphism ηiso
