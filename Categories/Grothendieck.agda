{-# OPTIONS --universe-polymorphism #-}
module Categories.Grothendieck where

open import Relation.Binary using (Rel)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

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
  ; assoc = assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = {! identityʳ !}
  ; equiv = record { 
     refl = refl , Het.refl;
     sym  = λ { (eq₁ , eq₂) → sym eq₁ , Het.sym eq₂}; 
     trans = λ { (xeq₁ , xeq₂) (yeq₁ , yeq₂) → trans xeq₁ yeq₁ , Het.trans xeq₂ yeq₂} }
  ; ∘-resp-≡ = {! ∘-resp-≡ !}
  }
  where
  open Functor F
  module Fc {c} where 
    open Category (F₀ c) public
    open Equiv public
  open Category C 
  open Equiv
  module Cat = Category (Categories o′ ℓ′ e′)
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
    Het.≡⇒∼ eq ≣-refl
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

  .assoc′ : {A B C₁ D : Obj′} {f : Hom′ A B} {g : Hom′ B C₁} {h : Hom′ C₁ D} →
                 ((h ∘′ g) ∘′ f) ≡′ (h ∘′ (g ∘′ f))
  assoc′ {ca , xa} {cb , xb} {cc , xc} {cd , xd} {f , α} {g , β} {h , γ} 
    = assoc , (Het.≡⇒∼ eq ≣-refl 
      (Fc.trans (coerce-resp-≡ eq ≣-refl Fc.assoc) 
      (Fc.trans (Fc.sym (Fc.sym (coerce-∘ eq eqO ≣-refl γ (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘
                                                              coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α))))) 
      (Fc.∘-resp-≡ʳ mainp))))
   where
    open Fc.HomReasoning
    open Cong renaming (coerce to coe)
    eq : Functor.F₀ (F₁ ((h ∘ g) ∘ f)) xa ≣ Functor.F₀ (F₁ (h ∘ g ∘ f)) xa
    eq = (≡⇒≣ (F₁ ((h ∘ g) ∘ f)) (F₁ (h ∘ g ∘ f)) (F-resp-≡ (assoc {f = f})) xa)
    eq0 : Functor.F₀ (F₁ h Cat.∘ F₁ g) xb ≣ Functor.F₀ (F₁ (h ∘ g)) xb
    eq0 = (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ (h ∘ g)) (F₁ h Cat.∘ F₁ g) (homomorphism {f = g} {g = h})
                  xb)))
    eq1 : Functor.F₀ (F₁ (h ∘ g) Cat.∘ F₁ f) xa ≣ Functor.F₀ (F₁ ((h ∘ g) ∘ f)) xa
    eq1 = (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ ((h ∘ g) ∘ f)) (F₁ (h ∘ g) Cat.∘ F₁ f) (homomorphism {f = f} {g = h ∘ g})
                  xa)))
    eq2 : Functor.F₀ (F₁ h Cat.∘ F₁ (g ∘ f)) xa ≣ Functor.F₀ (F₁ (h ∘ g ∘ f)) xa
    eq2 = (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ (h ∘ g ∘ f)) (F₁ h Cat.∘ F₁ (g ∘ f)) (homomorphism {f = g ∘ f} {g = h})
                  xa)))
    eq3 : Functor.F₀ (F₁ g) (Functor.F₀ (F₁ f) xa) ≣ Functor.F₀ (F₁ (g ∘ f)) xa
    eq3 = (≣-relevant
                (≣-sym
                 (≡⇒≣ (F₁ (g ∘ f)) (F₁ g Cat.∘ F₁ f) (homomorphism {f = f} {g = g})
                  xa)))

    O : Category.Obj (F₀ cd)
    O = Functor.F₀ (F₁ h) xc
    eqO : Functor.F₀ (F₁ h) xc ≣ O
    eqO = ≣-refl
    
    lemma : ∀ {c1 c2} -> (F : Functor (F₀ c1) (F₀ c2)) {X₁ X₂ Y₁ Y₂ : Category.Obj (F₀ c1)} → 
              (xeq : X₁ ≣ X₂) (yeq : Y₁ ≣ Y₂) (f : X₁ Fc.⇒ Y₁) → Functor.F₁ F (coe xeq yeq f) Fc.≡ 
              coe (≣-cong (Functor.F₀ F) xeq) (≣-cong (Functor.F₀ F) yeq) (Functor.F₁ F f)
    lemma F ≣-refl ≣-refl f = Fc.refl

    mainp2 : coe eq2 ≣-refl (Functor.F₁ (F₁ h) (β Fc.∘ coe eq3 ≣-refl (Functor.F₁ (F₁ g) α))) Fc.≡ 
              Functor.F₁ (F₁ h) β Fc.∘ coe (≣-trans eq1 eq) (≣-sym eq0) (Functor.F₁ (F₁ (h ∘ g)) α)  
    mainp2 = begin 
      coe eq2 ≣-refl (Functor.F₁ (F₁ h) (β Fc.∘ coe eq3 ≣-refl (Functor.F₁ (F₁ g) α)))
       ↓⟨ coerce-resp-≡ eq2 ≣-refl (Functor.homomorphism (F₁ h)) ⟩ 
      coe eq2 ≣-refl
       (Functor.F₁ (F₁ h) β Fc.∘
        Functor.F₁ (F₁ h) (coe eq3 ≣-refl (Functor.F₁ (F₁ g) α)))
       ↓⟨ coerce-∘ eq2 ≣-refl ≣-refl (Functor.F₁ (F₁ h) β)
            (Functor.F₁ (F₁ h) (coe eq3 ≣-refl (Functor.F₁ (F₁ g) α))) ⟩ 
      Functor.F₁ (F₁ h) β Fc.∘
      coe eq2 ≣-refl
      (Functor.F₁ (F₁ h) (coe eq3 ≣-refl (Functor.F₁ (F₁ g) α)))
      ↓⟨ Fc.refl ⟩∘⟨ coerce-resp-≡ eq2 ≣-refl
                       (lemma (F₁ h) eq3 ≣-refl (Functor.F₁ (F₁ g) α)) ⟩ 
      Functor.F₁ (F₁ h) β Fc.∘
        coe eq2 ≣-refl
        (coe eq4 ≣-refl (Functor.F₁ (F₁ h) (Functor.F₁ (F₁ g) α))) ↓⟨ Fc.refl ⟩∘⟨ Fc.sym (coerce-trans eq4 eq2 ≣-refl ≣-refl _) ⟩ 
      Functor.F₁ (F₁ h) β Fc.∘
        coe (≣-trans eq4 eq2) ≣-refl
        (Functor.F₁ (F₁ h) (Functor.F₁ (F₁ g) α))
        ↓⟨ Fc.refl ⟩∘⟨ coerce-resp-≡ (≣-trans eq4 eq2) ≣-refl (Fc.sym (Het.∼⇒≡₂ (OHet.ohet⇒het (homomorphism α)) eq5 eq6)) ⟩ 
      Functor.F₁ (F₁ h) β Fc.∘
        coe (≣-trans eq4 eq2) ≣-refl
        (coe eq5 eq6 (Functor.F₁ (F₁ (h ∘ g)) α))
        ↓⟨ Fc.refl ⟩∘⟨ Fc.sym (coerce-trans eq5 (≣-trans eq4 eq2) eq6 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)) ⟩ 
      Functor.F₁ (F₁ h) β Fc.∘
        coe (≣-trans eq5 (≣-trans eq4 eq2)) (≣-trans eq6 ≣-refl)
        (Functor.F₁ (F₁ (h ∘ g)) α)
        ↓⟨ Fc.refl ⟩∘⟨ coerce-invariant (≣-trans eq5 (≣-trans eq4 eq2)) (≣-trans eq1 eq) (≣-trans eq6 ≣-refl) eq6 (Functor.F₁ (F₁ (h ∘ g)) α) ⟩ 
      _ ∎
     where
      eq4 = (≣-cong (Functor.F₀ (F₁ h)) eq3)
      eq5 : Functor.F₀ (F₁ (C [ h ∘ g ])) (Functor.F₀ (F₁ f) xa) ≣
              Functor.F₀ (Categories o′ ℓ′ e′ [ F₁ h ∘ F₁ g ])
              (Functor.F₀ (F₁ f) xa)
      eq5 = Het.domain-≣ (OHet.ohet⇒het (homomorphism α))
      eq6 : Functor.F₀ (F₁ (C [ h ∘ g ])) xb ≣
              Functor.F₀ (Categories o′ ℓ′ e′ [ F₁ h ∘ F₁ g ]) xb
      eq6 = ≣-sym eq0

    mainp : coe eq eqO (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘ (coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)))
             Fc.≡ (coe eq2 ≣-refl (Functor.F₁ (F₁ h) (proj₂ ((g , β) ∘′ (f , α)))))
    mainp = begin 
     (coe eq ≣-refl
        (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘
         coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α))
       ↓⟨ coerce-∘ eq (≣-sym eq0) ≣-refl (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β)) (coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)) ⟩ 
     coe (≣-sym eq0) ≣-refl (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β)) Fc.∘ coe eq (≣-sym eq0) (coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)) 
       ↓⟨ coerce-zigzag eq0 (≣-sym eq0) ≣-refl ≣-refl {Functor.F₁ (F₁ h) β} ⟩∘⟨ 
          Fc.sym (coerce-trans eq1 eq ≣-refl (≣-sym eq0) (Functor.F₁ (F₁ (h ∘ g)) α)) ⟩ 
     Functor.F₁ (F₁ h) β Fc.∘ coe (≣-trans eq1 eq) (≣-sym eq0) (Functor.F₁ (F₁ (h ∘ g)) α) 
       ↓⟨ Fc.sym mainp2 ⟩ 
     (coe eq2 ≣-refl (Functor.F₁ (F₁ h) (proj₂ ((g , β) ∘′ (f , α)))) ∎))

