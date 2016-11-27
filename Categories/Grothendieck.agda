{-# OPTIONS --universe-polymorphism #-}
module Categories.Grothendieck where

open import Relation.Binary using (Rel)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import Categories.Support.Experimental
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

Dom : ∀ {o ℓ e o′} {C : Category o ℓ e} → (F : Functor C (Sets o′)) -> Functor (Elements F) C
Dom {C = C} F = record {
                  F₀ = proj₁;
                  F₁ = proj₁′;
                  identity = Equiv.refl;
                  homomorphism = Equiv.refl;
                  F-resp-≡ = λ x → x }
  where
   open Category C

-- because we want the following function to reduce all the time, define it globally
private
  module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} (F : Functor C (Categories o′ ℓ′ e′)) where
    private
      module C = Category C
      module F = Functor F
      module Cat = Category (Categories o′ ℓ′ e′)
    
    ∘-eq : ∀ {cx xx cy cz} -> (f : cy C.⇒ cz) (g : cx C.⇒ cy) -> Functor.F₀ (F.F₁ f Cat.∘ F.F₁ g) xx ≣ Functor.F₀ (F.F₁ (f C.∘ g)) xx
    ∘-eq {cx} {xx} {cy} {cz} f g = ≣-relevant (≣-sym (≡⇒≣ (F.F₁ (f C.∘ g)) (F.F₁ f Cat.∘ F.F₁ g) (F.homomorphism {f = g} {g = f}) xx))

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
  module Groth where
  open Functor F
  module Fc {c} where
    open Category (F₀ c) public
    open Equiv public
  open Category C
  open Equiv
  module Cat = Category (Categories o′ ℓ′ e′)
  module Cong {c} where
   open Congruence (TrivialCongruence (F₀ c)) public
  open Cong public using () renaming (coerce to coe) 
  module Het {c} = Heterogeneous (TrivialCongruence (F₀ c))
  open Het using (▹_)
  module OHet {c} where
   open CCat.Heterogeneous (F₀ c) public
   ohet⇒het : ∀ {A B} {f : A Fc.⇒ B} -> ∀ {X Y} → {g : X Fc.⇒ Y} → f ∼ g -> f Het.∼ g
   ohet⇒het (≡⇒∼ x) = Het.≡⇒∼ ≣-refl ≣-refl x

  Obj′ = Σ Obj (\ c -> Category.Obj (F₀ c))
  
  Hom′ : Rel Obj′ _
  Hom′ (c₁ , x₁) (c₂ , x₂) = Σ (c₁ ⇒ c₂) (λ f → Functor.F₀ (F₁ f) x₁ Fc.⇒ x₂)

  _≡′_ : ∀ {X Y} → Rel (Hom′ X Y) _
  _≡′_ {c₁ , x₁} {c₂ , x₂} (f , α) (g , β) = f ≡ g × α Het.∼ β

  _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
  _∘′_ {cx , xx} {Y} {cz , xz} (f , α) (g , β) = (f ∘ g) , α Fc.∘ Cong.coerce (∘-eq F f g) ≣-refl (Functor.F₁ (F₁ f) β)

  id-eq : ∀ {c x} -> Functor.F₀ (Cat.id {F₀ c}) x ≣ Functor.F₀ (F₁ id) x
  id-eq {c} {x} = ≣-relevant (≣-sym (≡⇒≣ (F₁ id) Cat.id (identity {c}) x))

  id′ : {A : Obj′} → Hom′ A A
  id′ {c , x} = id , Cong.coerce id-eq ≣-refl Fc.id

  F-resp-∼ : ∀ {b c} -> (H : Functor (F₀ b) (F₀ c)) -> {A B A' B' : Category.Obj (F₀ b)} {α : A Fc.⇒ B }{β : A' Fc.⇒ B'} →
             (α Het.∼ β) → (Functor.F₁ H α Het.∼ Functor.F₁ H β)
  F-resp-∼ H (Heterogeneous.≡⇒∼ ≣-refl ≣-refl x) = Heterogeneous.≡⇒∼ ≣-refl ≣-refl (Functor.F-resp-≡ H x)

  .identityˡ′ : {A B : Obj′} {f : Hom′ A B} → (id′ ∘′ f) ≡′ f
  identityˡ′ {ca , xa} {cb , xb} {f , α} = identityˡ , (begin
    ▹ coe id-eq ≣-refl Fc.id Fc.∘ coe (∘-eq F id f) ≣-refl (Functor.F₁ (F₁ id) α)
      ↓⟨ Het.∘-resp-∼ (Het.sym (Het.coerce-resp-∼ id-eq ≣-refl)) F₁id[α]~α ⟩
    ▹ Fc.id Fc.∘ α 
      ↓⟨ Het.≡⇒∼ ≣-refl ≣-refl Fc.identityˡ ⟩
    ▹ α 
      ∎)
   where
    open Het.HetReasoning
    F₁id[α]~α : coe (∘-eq F id f) ≣-refl (Functor.F₁ (F₁ id) α) Het.∼ α
    F₁id[α]~α = begin 
      ▹ coe (∘-eq F id f) ≣-refl (Functor.F₁ (F₁ id) α) 
        ↑⟨ Het.coerce-resp-∼ (∘-eq F id f) ≣-refl ⟩ 
      ▹ Functor.F₁ (F₁ id) α 
        ↓⟨ OHet.ohet⇒het (identity α) ⟩ 
      ▹ α 
        ∎

  .identityʳ′ : {A B : Obj′} {f : Hom′ A B} → (f ∘′ id′) ≡′ f
  identityʳ′ {ca , xa} {cb , xb} {f , α} = identityʳ , (begin 
    ▹ α Fc.∘ coe (∘-eq F f id) ≣-refl (Functor.F₁ (F₁ f) (coe id-eq ≣-refl Fc.id))
       ↓⟨ Het.∘-resp-∼ʳ F₁f[id]~id ⟩ 
    ▹ α Fc.∘ Fc.id
       ↓⟨ Het.≡⇒∼ ≣-refl ≣-refl Fc.identityʳ ⟩ 
    ▹ α                                                
       ∎)
   where
    open Het.HetReasoning
    F₁f[id]~id : coe (∘-eq F f id) ≣-refl (Functor.F₁ (F₁ f) (coe id-eq ≣-refl Fc.id)) Het.∼ Fc.id
    F₁f[id]~id = begin 
      ▹ coe (∘-eq F f id) ≣-refl (Functor.F₁ (F₁ f) (coe id-eq ≣-refl Fc.id))
        ↑⟨ Het.coerce-resp-∼ (∘-eq F f id) ≣-refl ⟩ 
      ▹ Functor.F₁ (F₁ f) (coe id-eq ≣-refl Fc.id)
        ↓⟨ F-resp-∼ (F₁ f) (Het.sym (Het.coerce-resp-∼ id-eq ≣-refl)) ⟩
      ▹ Functor.F₁ (F₁ f) (Category.id (F₀ ca)) 
        ↓⟨ Het.≡⇒∼ ≣-refl ≣-refl (Functor.identity (F₁ f)) ⟩
      ▹ Fc.id
        ∎

  .assoc′ : {A B C₁ D : Obj′} {f : Hom′ A B} {g : Hom′ B C₁} {h : Hom′ C₁ D} →
                 ((h ∘′ g) ∘′ f) ≡′ (h ∘′ (g ∘′ f))
  assoc′ {ca , xa} {cb , xb} {cc , xc} {cd , xd} {f , α} {g , β} {h , γ} 
    = assoc , Het.trans (Het.≡⇒∼ ≣-refl ≣-refl Fc.assoc) (Het.∘-resp-∼ʳ F₁h[β]∘F₁h∘g[α]~F₁h[β∘F₁g[α]])
   where
    open Het.HetReasoning
    eq : Functor.F₀ (F₁ ((h ∘ g) ∘ f)) xa ≣ Functor.F₀ (F₁ (h ∘ g ∘ f)) xa
    eq = ≡⇒≣ (F₁ ((h ∘ g) ∘ f)) (F₁ (h ∘ g ∘ f)) (F-resp-≡ (assoc {f = f})) xa

    F₁h[β]∘F₁h∘g[α]~F₁h[β∘F₁g[α]] : (coe (∘-eq F h g) ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘ coe (∘-eq F (h ∘ g) f) ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α))
                                     Het.∼ (coe (∘-eq F h (g ∘ f)) ≣-refl (Functor.F₁ (F₁ h) (proj₂ ((g , β) ∘′ (f , α)))))
    F₁h[β]∘F₁h∘g[α]~F₁h[β∘F₁g[α]] = Het.sym (begin 
      ▹ coe (∘-eq F h (g ∘ f)) ≣-refl (Functor.F₁ (F₁ h) (β Fc.∘ coe(∘-eq F g f) ≣-refl (Functor.F₁ (F₁ g) α)))
        ↑⟨ Het.coerce-resp-∼ (∘-eq F h (g ∘ f)) ≣-refl ⟩
      ▹ Functor.F₁ (F₁ h) (β Fc.∘ coe (∘-eq F g f) ≣-refl (Functor.F₁ (F₁ g) α))
        ↓⟨ Het.≡⇒∼ ≣-refl ≣-refl (Functor.homomorphism (F₁ h)) ⟩
      ▹ Functor.F₁ (F₁ h) β Fc.∘ (Functor.F₁ (F₁ h) (coe (∘-eq F g f) ≣-refl (Functor.F₁ (F₁ g) α)))
        ↓⟨ Het.∘-resp-∼ (Het.coerce-resp-∼ (∘-eq F h g) ≣-refl) F₁h[β]~F₁h∘g[α] ⟩
      ▹ coe (∘-eq F h g) ≣-refl (Functor.F₁ (F₁ h) β) Fc.∘ coe (∘-eq F (h ∘ g) f) ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)
        ∎)
     where
      F₁h[β]~F₁h∘g[α] : (Functor.F₁ (F₁ h) (coe (∘-eq F g f) ≣-refl (Functor.F₁ (F₁ g) α))) Het.∼ coe (∘-eq F (h ∘ g) f) ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α)
      F₁h[β]~F₁h∘g[α] = begin
        ▹ Functor.F₁ (F₁ h) (coe (∘-eq F g f) ≣-refl (Functor.F₁ (F₁ g) α))
          ↓⟨ F-resp-∼ (F₁ h) (Het.sym (Het.coerce-resp-∼ (∘-eq F g f) ≣-refl)) ⟩ 
        ▹ Functor.F₁ (F₁ h) (Functor.F₁ (F₁ g) α)
          ↑⟨ OHet.ohet⇒het (homomorphism α) ⟩ 
        ▹ Functor.F₁ (F₁ (h ∘ g)) α 
          ↓⟨ Het.coerce-resp-∼ (∘-eq F (h ∘ g) f) ≣-refl ⟩ 
        ▹ coe (∘-eq F (h ∘ g) f) ≣-refl (Functor.F₁ (F₁ (h ∘ g)) α) 
          ∎

  .∘-resp-≡′ : {A B C₁ : Obj′} {f h : Hom′ B C₁} {g i : Hom′ A B} →
                     f ≡′ h → g ≡′ i → (f ∘′ g) ≡′ (h ∘′ i)
  ∘-resp-≡′ {a , ax} {b , bx} {c , cx} {f = f , α} {h , η} {g , γ} {i , ι} (f≡h , α~η) (g≡i , γ~ι) = ∘-resp-≡ f≡h g≡i , Het.∘-resp-∼ α~η 
    (begin 
     ▹ coe (∘-eq F f g) ≣-refl (Functor.F₁ (F₁ f) γ) ↑⟨ Het.coerce-resp-∼ (∘-eq F f g) ≣-refl ⟩
     ▹ Functor.F₁ (F₁ f) γ                           ↓⟨ OHet.ohet⇒het (F-resp-≡ f≡h γ) ⟩
     ▹ Functor.F₁ (F₁ h) γ                           ↓⟨ F-resp-∼ (F₁ h) γ~ι ⟩
     ▹ Functor.F₁ (F₁ h) ι                           ↓⟨ Het.coerce-resp-∼ (∘-eq F h i) ≣-refl ⟩
     ▹ coe (∘-eq F h i) ≣-refl (Functor.F₁ (F₁ h) ι) ∎)
   where
    open Het.HetReasoning

Gr = Grothendieck

DomGr : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} → (F : Functor C (Categories o′ ℓ′ e′)) → Functor (Grothendieck F) C
DomGr {C = C} F = record {
                    F₀ = proj₁;
                    F₁ = proj₁;
                    identity = C.Equiv.refl;
                    homomorphism = C.Equiv.refl;
                    F-resp-≡ = proj₁ }
  where 
    module C = Category C

inGr : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} (F : Functor C (Categories o′ ℓ′ e′)) → ∀ c -> Functor (Functor.F₀ F c) (Gr F)
inGr {C = C} F c = record {
                     F₀ = _,_ c;
                     F₁ = λ f → C.id , GrF.coe GrF.id-eq ≣-refl f;
                     identity = Category.Equiv.refl (Grothendieck F);
                     homomorphism = C.Equiv.sym C.identityʳ , Het.trans (Het.sym (Het.coerce-resp-∼ GrF.id-eq ≣-refl))
                                                                (Het.∘-resp-∼ (Het.coerce-resp-∼ GrF.id-eq ≣-refl)
                                                                 (Het.trans
                                                                  (Het.trans (Het.coerce-resp-∼ GrF.id-eq ≣-refl)
                                                                   (Het.sym (GrF.OHet.ohet⇒het (F.identity _))))
                                                                  (Het.coerce-resp-∼ (∘-eq F C.id C.id) ≣-refl)));
                     F-resp-≡ = λ x → C.Equiv.refl , (Het.trans (Het.trans (Het.sym (Het.coerce-resp-∼ GrF.id-eq ≣-refl)) 
                              (Heterogeneous.≡⇒∼ ≣-refl ≣-refl x)) (Het.coerce-resp-∼ GrF.id-eq ≣-refl)) }
  where
    module C = Category C
    module F = Functor F
    module GrF = Groth F
    open GrF using (module Het; module Cong)
