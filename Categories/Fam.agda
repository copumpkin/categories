module Categories.Fam where

open import Level
open import Relation.Binary using (Rel)
import Relation.Binary.HeterogeneousEquality as Het
open Het using (_≅_) renaming (refl to ≣-refl)

open import Categories.Support.PropositionalEquality

open import Categories.Category

module Fam {a b : Level} where
  record Fam : Set (suc a ⊔ suc b) where
      constructor _,_
      field
        U : Set a 
        T : U → Set b
  open Fam public

  record Hom (A B : Fam) : Set (a ⊔ b) where
    constructor _,_
    field
      f : U A → U B
      φ : (x : U A) → T A x → T B (f x)

  record _≡Fam_ {X Y} (f g : (Hom X Y)) : Set (a ⊔ b) where
      constructor _,_
      field
        f≡g : {x : _} → Hom.f f x ≣ Hom.f g x
        φ≡γ : {x : _} {bx : _} → Hom.φ f x bx ≅ Hom.φ g x bx

  module Eq = _≡Fam_

  Cat : Category (suc a ⊔ suc b) (a ⊔ b) (a ⊔ b)
  Cat = record {
                Obj = Fam;
                _⇒_ = Hom;
                _≡_ = _≡Fam_;
                id = id′;
                _∘_ = _∘′_;
                assoc = ≣-refl , ≣-refl;
                identityˡ = ≣-refl , ≣-refl;
                identityʳ = ≣-refl , ≣-refl;
                equiv = record {
                  refl  = ≣-refl , ≣-refl;
                  sym   = \ { (f≡g , φ≡γ) → ≣-sym f≡g , Het.sym φ≡γ }; 
                  trans = λ {(f≡g , φ≡γ) (g≡h , γ≡η) → ≣-trans f≡g g≡h , Het.trans φ≡γ γ≡η} };
                ∘-resp-≡ = ∘-resp-≡′ }
   where
     id′ : {A : Fam} → Hom A A
     id′ = (\ x → x) , (\ x bx → bx)
 
     _∘′_ : {A B C : Fam} → Hom B C → Hom A B → Hom A C
     _∘′_ (f , φ) (g , γ) = (λ x → f (g x)) , (λ x bx → φ (g x) (γ x bx))
  
     sym′ : ∀ {X Y} → Relation.Binary.Symmetric (_≡Fam_ {X} {Y})
     sym′ {Ax , Bx} {Ay , By} {f , φ} {g , γ} (f≡g , φ≡γ) = ≣-sym f≡g , Het.sym φ≡γ

     ∘-resp-≡′ : {A B C : Fam} {f h : Hom B C} {g i : Hom A B} → f ≡Fam h → g ≡Fam i → (f ∘′ g) ≡Fam (h ∘′ i)
     ∘-resp-≡′ {f = (f , φ)} {g , γ} {h , η} {i , ι} (f≡g , φ≡γ) (h≡i , η≡ι) = 
       ≣-trans f≡g (≣-cong g h≡i) , Het.trans φ≡γ (Het.cong₂ γ (Het.≡-to-≅ h≡i) η≡ι)

  open Category Cat public


Fam : ∀ a b → Category (suc a ⊔ suc b) (a ⊔ b) (a ⊔ b)
Fam a b = Fam.Cat {a} {b}
