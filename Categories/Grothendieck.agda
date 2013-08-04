{-# OPTIONS --universe-polymorphism #-}
module Categories.Grothendieck where

open import Relation.Binary using (Rel)
open import Data.Product using (Σ; _,_; proj₂; _×_)

open import Categories.Support.PropositionalEquality
open import Categories.Support.IProduct
import Categories.Category as CCat
open CCat hiding (module Heterogeneous)
open import Categories.Functor using (Functor; module Functor; ≡⇒≣)
open import Categories.Agda
{-
-- TODO: don't use sigmas
-- Break into modules Strict and Weak using Sets and Setoids?
Grothendieck : ∀ {o ℓ e o′} {C : Category o ℓ e} → Functor C (Sets o′) → Category _ _ _
Grothendieck {o′ = o′} {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id , identity
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  open Category C
  open Equiv
  open Functor F

  Obj′ = Σ Obj F₀
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ′ (c₁ ⇒ c₂) (λ f → F₁ f x₁ ≣ x₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  (f , pf₁) ≡′ (g , pf₂) = f ≡ g

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {X} {Y} {Z} (f , pf₁) (g , pf₂) = (f ∘ g) , pf
    where
    -- This could be a lot prettier...
    .pf : F₁ (f ∘ g) (proj₂ X) ≣ proj₂ Z
    pf = ≣-trans homomorphism (≣-sym (≣-trans (≣-sym pf₁) (≣-cong (F₁ f) (≣-sym pf₂))))

-}
open import Categories.Categories
open import Categories.Congruence

Grothendieck2 : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} → Functor C (Categories o′ ℓ′ e′) → Category _ _ _
Grothendieck2 {o′ = o′} {ℓ′} {e′} {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = {! assoc !}
  ; identityˡ = {! identityˡ !}
  ; identityʳ = {! identityʳ !}
  ; equiv = {! record
    { refl = refl
    ; sym = sym
    ; trans = trans
    } !}
  ; ∘-resp-≡ = {! ∘-resp-≡ !}
  }
  where
  open Category C 
  open Equiv
  open Functor F
  module Cat = Category (Categories o′ ℓ′ e′)
  module Fc {c} = Category (F₀ c)
  module Cong {c} where
   open Congruence (TrivialCongruence (F₀ c)) public
  module Het {c} = Heterogeneous (TrivialCongruence (F₀ c))
  module OHet {c} where
   open CCat.Heterogeneous (F₀ c) public
   ohet⇒het : ∀ {A B} {f : A Fc.⇒ B} -> ∀ {X Y} → {g : X Fc.⇒ Y} → f ∼ g -> f Het.∼ g
   ohet⇒het (≡⇒∼ x) = Het.≡⇒∼ ≣-refl ≣-refl x

  postulate ≣-relevant : ∀ {l} {A : Set l} {X Y : A} -> .(X ≣ Y) -> X ≣ Y

  Obj′ = Σ Obj (\ c -> Category.Obj (F₀ c))
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ (c₁ ⇒ c₂) (λ f → Functor.F₀ (F₁ f) x₁ Fc.⇒ x₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  _≡′_ {c₁ , x₁} {c₂ , x₂} (f , α) (g , β) = f ≡ g × α Het.∼ β

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {cx , xx} {Y} {cz , xz} (f , α) (g , β) = (f ∘ g) , α Fc.∘ Cong.coerce 
             (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ (f ∘ g)) (F₁ f Cat.∘ F₁ g) (homomorphism {f = g} {g = f})
                  xx))) ≣-refl
                   (Functor.F₁ (F₁ f) β)

  id′ : {A : Obj′} → Hom′ A A
  id′ {c , x} = id , Cong.coerce (≣-relevant (≣-sym (≡⇒≣ (F₁ id) Cat.id (identity {c}) x))) ≣-refl Fc.id

  .identityˡ′ : {A B : Obj′} {f : Hom′ A B} → (id′ ∘′ f) ≡′ f
  identityˡ′ {ca , xa} {cb , xb} {f , α} = identityˡ , 
    Het.≡⇒∼ (≣-relevant (≡⇒≣ (F₁ (id ∘ f)) (F₁ f) (F-resp-≡ (identityˡ {f = f})) xa)) ≣-refl
    (begin 
     coe eq ≣-refl
         (coe eq0 ≣-refl Fc.id 
          Fc.∘ coe eq1 ≣-refl (Functor.F₁ (F₁ id) α))                   ↓⟨ coerce-∘ eq (≣-sym eq0) ≣-refl (coe eq0 ≣-refl Fc.id)
                                                                            (coe eq1 ≣-refl (Functor.F₁ (F₁ id) α)) ⟩
     coe (≣-sym eq0) ≣-refl (coe eq0 ≣-refl Fc.id) 
      Fc.∘ (coe eq (≣-sym eq0) (coe eq1 ≣-refl (Functor.F₁ (F₁ id) α))) ↑⟨ Fc.∘-resp-≡ (coerce-trans eq0 (≣-sym eq0) ≣-refl ≣-refl Fc.id)
                                                                            (coerce-trans eq1 eq ≣-refl (≣-sym eq0) (Functor.F₁ (F₁ id) α)) ⟩ 
     coe (≣-trans eq0 (≣-sym eq0)) ≣-refl Fc.id 
      Fc.∘ coe (≣-trans eq1 eq) (≣-sym eq0) (Functor.F₁ (F₁ id) α)      ↓⟨ Fc.∘-resp-≡ˡ (coerce-invariant (≣-trans eq0 (≣-sym eq0)) 
                                                                                  ≣-refl ≣-refl ≣-refl Fc.id) ⟩ 
     Fc.id Fc.∘ coe (≣-trans eq1 eq) (≣-sym eq0) (Functor.F₁ (F₁ id) α) ↓⟨ Fc.identityˡ ⟩ 
     coe (≣-trans eq1 eq) (≣-sym eq0) (Functor.F₁ (F₁ id) α)            ↓⟨ Het.∼⇒≡₂ (OHet.ohet⇒het (identity α)) (≣-trans eq1 eq) (≣-sym eq0) ⟩ 
     α                                                                  ∎)
   where
    open Fc.HomReasoning
    open Cong renaming (coerce to coe)
    eq0 : Functor.F₀ (Cat.id {F₀ cb}) xb ≣ Functor.F₀ (F₁ id) xb
    eq0 = (≣-relevant (≣-sym (≡⇒≣ (F₁ id) Cat.id (identity {cb}) xb)))
    eq1 : Functor.F₀ (F₁ id Cat.∘ F₁ f) xa ≣ Functor.F₀ (F₁ (id ∘ f)) xa
    eq1 = (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ (id ∘ f)) (F₁ id Cat.∘ F₁ f) (homomorphism {f = f} {g = id})
                  xa)))
    eq : Functor.F₀ (F₁ (id ∘ f)) xa ≣ Functor.F₀ (F₁ f) xa
    eq = (≣-relevant (≡⇒≣ (F₁ (id ∘ f)) (F₁ f) (F-resp-≡ (identityˡ {f = f})) xa))
    
