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
open import Categories.Categories
open import Categories.Congruence


-- TODO: don't use sigmas
-- Break into modules Strict and Weak using Sets and Setoids?
Elements : ∀ {o ℓ e o′} {C : Category o ℓ e} → Functor C (Sets o′) → Category _ _ _
Elements {o′ = o′} {C = C} F = record 
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


Grothendieck : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} → Functor C (Categories o′ ℓ′ e′) → Category _ _ _
Grothendieck {o′ = o′} {ℓ′} {e′} {C = C} F = record 
  { Obj = Obj′
  ; _⇒_ = Hom′
  ; _≡_ = _≡′_
  ; _∘_ = _∘′_
  ; id = id′
  ; assoc = assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; equiv = record { 
     refl = refl , Het.refl;
     sym  = λ { (eq₁ , eq₂) → sym eq₁ , Het.sym eq₂}; 
     trans = λ { (xeq₁ , xeq₂) (yeq₁ , yeq₂) → trans xeq₁ yeq₁ , Het.trans xeq₂ yeq₂} }
  ; ∘-resp-≡ = ∘-resp-≡′
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

  ∘-eq : ∀ {cx xx cy cz} -> (f : cy ⇒ cz) (g : cx ⇒ cy) -> Functor.F₀ (F₁ f Cat.∘ F₁ g) xx ≣ Functor.F₀ (F₁ (f ∘ g)) xx
  ∘-eq {cx}{xx}{cy}{cz} f g = ≣-relevant (≣-sym (≡⇒≣ (F₁ (f ∘ g)) (F₁ f Cat.∘ F₁ g) (homomorphism {f = g} {g = f}) xx))

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {cx , xx} {Y} {cz , xz} (f , α) (g , β) = (f ∘ g) , α Fc.∘ Cong.coerce (∘-eq f g) ≣-refl (Functor.F₁ (F₁ f) β)

  id-eq : ∀ {c x} -> Functor.F₀ (Cat.id {F₀ c}) x ≣ Functor.F₀ (F₁ id) x
  id-eq {c} {x} = (≣-relevant (≣-sym (≡⇒≣ (F₁ id) Cat.id (identity {c}) x)))

  id′ : {A : Obj′} → Hom′ A A
  id′ {c , x} = id , Cong.coerce id-eq ≣-refl Fc.id

  F-resp-∼ : ∀ {b c} -> (H : Functor (F₀ b) (F₀ c)) -> {A B A' B' : Category.Obj (F₀ b)} {α : A Fc.⇒ B }{β : A' Fc.⇒ B'} →
             (α Het.∼ β) → (Functor.F₁ H α Het.∼ Functor.F₁ H β)
  F-resp-∼ H (Heterogeneous.≡⇒∼ ≣-refl ≣-refl x) = Heterogeneous.≡⇒∼ ≣-refl ≣-refl (Functor.F-resp-≡ H x)

  .identityˡ′ : {A B : Obj′} {f : Hom′ A B} → (id′ ∘′ f) ≡′ f
  identityˡ′ {ca , xa} {cb , xb} {f , α} = identityˡ , 
    Het.trans (Het.∘-resp-∼ (Het.sym (Het.coerce-resp-∼ id-eq ≣-refl)) 
                            (Het.trans (Het.sym (Het.coerce-resp-∼ (∘-eq id f) ≣-refl)) 
                                       (OHet.ohet⇒het (identity α)))) 
              (Het.≡⇒∼ ≣-refl ≣-refl Fc.identityˡ)
   where
    open Fc.HomReasoning
    open Cong renaming (coerce to coe)

  .assoc′ : {A B C₁ D : Obj′} {f : Hom′ A B} {g : Hom′ B C₁} {h : Hom′ C₁ D} →
                 ((h ∘′ g) ∘′ f) ≡′ (h ∘′ (g ∘′ f))
  assoc′ {ca , xa} {cb , xb} {cc , xc} {cd , xd} {f , α} {g , β} {h , γ} 
    = assoc , Het.trans (Het.≡⇒∼ ≣-refl ≣-refl Fc.assoc) (Het.∘-resp-∼ʳ mainp)
   where
    open Fc.HomReasoning
    open Cong renaming (coerce to coe)
    eq : Functor.F₀ (F₁ ((h ∘ g) ∘ f)) xa ≣ Functor.F₀ (F₁ (h ∘ g ∘ f)) xa
    eq = (≡⇒≣ (F₁ ((h ∘ g) ∘ f)) (F₁ (h ∘ g ∘ f)) (F-resp-≡ (assoc {f = f})) xa)
    eq0 = ∘-eq h g
    eq1 = ∘-eq (h ∘ g) f
    eq2 = ∘-eq h (g ∘ f)
    eq3 = ∘-eq g f

    mainp : (coe eq0 ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘ coe eq1 ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α))
             Het.∼ (coe eq2 ≣-refl (Functor.F₁ (F₁ h) (proj₂ ((g , β) ∘′ (f , α)))))
    mainp = Het.sym (Het.trans (Het.sym (Het.coerce-resp-∼ eq2 ≣-refl)) 
                    (Het.trans (Het.≡⇒∼ ≣-refl ≣-refl (Functor.homomorphism (F₁ h))) 
                    (Het.∘-resp-∼ (Het.coerce-resp-∼ eq0 ≣-refl) 
                         (Het.trans (Het.trans (F-resp-∼ (F₁ h) (Het.sym (Het.coerce-resp-∼ eq3 ≣-refl))) 
                           (Het.sym (OHet.ohet⇒het (homomorphism α)))) (Het.coerce-resp-∼ eq1 ≣-refl)))))

  .∘-resp-≡′ : {A B C₁ : Obj′} {f h : Hom′ B C₁} {g i : Hom′ A B} →
                     f ≡′ h → g ≡′ i → (f ∘′ g) ≡′ (h ∘′ i)
  ∘-resp-≡′ {a , ax} {b , bx} {c , cx} {f = f , α} {h , η} {g , γ} {i , ι} (f≡h , α~η) (g≡i , γ~ι) = (∘-resp-≡ f≡h g≡i) , (Het.∘-resp-∼ α~η 
    (Het.trans (Het.sym (Het.coerce-resp-∼ (∘-eq f g) ≣-refl)) 
     (Het.trans 
     (Het.trans (OHet.ohet⇒het (F-resp-≡ f≡h γ)) 
     (F-resp-∼ (F₁ h) γ~ι)) 
     (Het.coerce-resp-∼ (∘-eq h i) ≣-refl))))

  .identityʳ′ : {A B : Obj′} {f : Hom′ A B} → (f ∘′ id′) ≡′ f
  identityʳ′ {ca , xa} {cb , xb} {f , α} = identityʳ , (Het.trans (Het.∘-resp-∼ʳ 
   (Het.trans (Het.sym (Het.coerce-resp-∼ (∘-eq f id) ≣-refl)) 
   (Het.trans (F-resp-∼ (F₁ f) (Het.sym (Het.coerce-resp-∼ id-eq ≣-refl))) 
              (Het.≡⇒∼ ≣-refl ≣-refl (Functor.identity (F₁ f)))))) 
   (Het.≡⇒∼ ≣-refl ≣-refl Fc.identityʳ))
   where
    open Fc.HomReasoning
    open Cong renaming (coerce to coe)
