{-# OPTIONS --universe-polymorphism #-}

module Categories.NaturalIsomorphism where

open import Level
open import Relation.Binary using (IsEquivalence)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Category
open import Categories.Functor hiding (id) renaming (_∘_ to _∘F_; _≡_ to _≡F_; equiv to equivF)
open import Categories.NaturalTransformation.Core hiding (_≡_; equiv; setoid)
open import Categories.NaturalTransformation using (_∘ˡ_; _∘ʳ_)
import Categories.Morphisms as Morphisms
open import Categories.Functor.Properties using (module FunctorsAlways)

record NaturalIsomorphism {o ℓ e o′ ℓ′ e′}
                          {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  open Morphisms D

  field
    .iso : ∀ X → Iso (⇒.η X) (⇐.η X)

equiv : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (NaturalIsomorphism {C = C} {D})
equiv {C = C} {D} = record 
  { refl = record
    { F⇒G = id
    ; F⇐G = id
    ; iso = λ _ → record 
      { isoˡ = D.identityˡ
      ; isoʳ = D.identityˡ
      }
    }
  ; sym = λ X → let module X Z = Morphisms.Iso (NaturalIsomorphism.iso X Z) in record
    { F⇒G = NaturalIsomorphism.F⇐G X
    ; F⇐G = NaturalIsomorphism.F⇒G X
    ; iso = λ Y → record 
      { isoˡ = X.isoʳ Y
      ; isoʳ = X.isoˡ Y
      }
    }
  ; trans = trans′
  }
  where
  module C = Category C
  module D = Category D
  open D hiding (id)

  trans′ : {x y z : Functor C D} → NaturalIsomorphism x y → NaturalIsomorphism y z → NaturalIsomorphism x z
  trans′ X Y = record 
    { F⇒G = F⇒G′
    ; F⇐G = F⇐G′
    ; iso = iso′
    }
    where
    F⇒G′ = NaturalIsomorphism.F⇒G Y ∘₁ NaturalIsomorphism.F⇒G X
    F⇐G′ = NaturalIsomorphism.F⇐G X ∘₁ NaturalIsomorphism.F⇐G Y

    .iso′ : (X : C.Obj) → _
    iso′ Z = record 
      { isoˡ = isoˡ′
      ; isoʳ = isoʳ′
      }
      where
      open NaturalIsomorphism
      open NaturalTransformation
      module Y Z = Morphisms.Iso (iso Y Z)
      module X Z = Morphisms.Iso (iso X Z)

      isoˡ′ : (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ≡ D.id
      isoˡ′ = begin
                (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z)
              ↓⟨ D.assoc ⟩
                η (F⇐G X) Z ∘ (η (F⇐G Y) Z ∘ (η (F⇒G Y) Z ∘ η (F⇒G X) Z))
              ↑⟨ D.∘-resp-≡ʳ D.assoc ⟩
                η (F⇐G X) Z ∘ ((η (F⇐G Y) Z ∘ η (F⇒G Y) Z) ∘ η (F⇒G X) Z)
              ↓⟨ D.∘-resp-≡ʳ (D.∘-resp-≡ˡ (Y.isoˡ Z)) ⟩
                η (F⇐G X) Z ∘ (D.id ∘ η (F⇒G X) Z)
              ↓⟨ D.∘-resp-≡ʳ D.identityˡ ⟩
                η (F⇐G X) Z ∘ η (F⇒G X) Z
              ↓⟨ X.isoˡ Z ⟩
                D.id
              ∎
        where
        open D.HomReasoning

      isoʳ′ : (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z) ≡ D.id
      isoʳ′ = begin
                (η (F⇒G Y) Z ∘ η (F⇒G X) Z) ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z)
              ↓⟨ D.assoc ⟩
                η (F⇒G Y) Z ∘ (η (F⇒G X) Z ∘ (η (F⇐G X) Z ∘ η (F⇐G Y) Z))
              ↑⟨ D.∘-resp-≡ʳ D.assoc ⟩
                η (F⇒G Y) Z ∘ ((η (F⇒G X) Z ∘ η (F⇐G X) Z) ∘ η (F⇐G Y) Z)
              ↓⟨ D.∘-resp-≡ʳ (D.∘-resp-≡ˡ (X.isoʳ Z)) ⟩
                η (F⇒G Y) Z ∘ (D.id ∘ η (F⇐G Y) Z)
              ↓⟨ D.∘-resp-≡ʳ D.identityˡ ⟩
                η (F⇒G Y) Z ∘ η (F⇐G Y) Z
              ↓⟨ Y.isoʳ Z ⟩
                D.id
              ∎
        where
        open D.HomReasoning

setoid : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Setoid _ _
setoid {C = C} {D} = record 
  { Carrier = Functor C D
  ; _≈_ = NaturalIsomorphism
  ; isEquivalence = equiv {C = C} {D}
  }

_ⓘˡ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (H : Functor D E) → (η : NaturalIsomorphism F G) → NaturalIsomorphism (H ∘F F) (H ∘F G)
_ⓘˡ_ {C = C} {D} {E} {F} {G} H η = record
  { F⇒G = H ∘ˡ η.F⇒G
  ; F⇐G = H ∘ˡ η.F⇐G
  ; iso = λ X → FunctorsAlways.resp-Iso H (η.iso X)
  }
  where
  module η = NaturalIsomorphism η

_ⓘʳ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (η : NaturalIsomorphism F G) → (K : Functor E C) → NaturalIsomorphism (F ∘F K) (G ∘F K)
η ⓘʳ K = record
  { F⇒G = η.F⇒G ∘ʳ K
  ; F⇐G = η.F⇐G ∘ʳ K
  ; iso = λ X → η.iso (K.F₀ X)
  }
  where
  module η = NaturalIsomorphism η
  module K = Functor K

-- try ≡→iso again, but via first de-embedding some helpers, as that seems to make things
-- go 'weird' in combination with irrelevance
private
  _©_ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} →
       NaturalTransformation F G → (x : Category.Obj C) → D [ Functor.F₀ F x , Functor.F₀ G x ]
  _©_ = NaturalTransformation.η
  
  my-sym : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) → F ≡F G → G ≡F F
  my-sym {D = D} _ _ F≡G X = Heterogeneous.sym D (F≡G X)

  oneway : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) →
    F ≡F G → NaturalTransformation F G
  oneway {C = C} {D} F G F≡G =
    record
    { η = my-η
    ; commute = my-commute
    }
    where
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    open Heterogeneous D
    same-Objs : ∀ A → F.F₀ A ≣ G.F₀ A
    same-Objs A = domain-≣ (F≡G (C.id {A}))
    my-η : ∀ X → D [ F.F₀ X , G.F₀ X ]
    my-η X = ≣-subst (λ x → D [ F.F₀ X , x ]) (same-Objs X) D.id

    .my-commute : ∀ {X Y} (f : C [ X , Y ]) → D [ D [ my-η Y ∘ F.F₁ f ] ≡ D [ G.F₁ f ∘ my-η X ] ]
    my-commute {X} {Y} f with helper₃
      where
      helper₁ : D [ my-η Y ∘ F.F₁ f ] ∼ F.F₁ f 
      helper₁ with F.F₀ Y | G.F₀ Y | same-Objs Y | F.F₁ f
      helper₁ | _ | ._ | ≣-refl | f′ = ≡⇒∼ D.identityˡ
      helper₂ : G.F₁ f ∼ D [ G.F₁ f ∘ my-η X ]
      helper₂ with F.F₀ X | G.F₀ X | same-Objs X | G.F₁ f
      helper₂ | _ | ._ | ≣-refl | f′ = ≡⇒∼ (D.Equiv.sym D.identityʳ)
      helper₃ : D [ my-η Y ∘ F.F₁ f ] ∼ D [ G.F₁ f ∘ my-η X ]
      helper₃ = trans helper₁ (trans (F≡G f) helper₂)
    my-commute f | Heterogeneous.≡⇒∼ pf = irr pf
    
≡→iso : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) → F ≡F G → NaturalIsomorphism F G
≡→iso {C = C} {D} F G F≡G =
  record
  { F⇒G = oneway F G F≡G
  ; F⇐G = oneway G F (my-sym F G F≡G)
  ; iso = λ X → record
    { isoˡ = my-iso G F (my-sym F G F≡G) F≡G X
    ; isoʳ = my-iso F G F≡G (my-sym F G F≡G) X
    }
  }
  where
  module C = Category C
  module D = Category D
  open Heterogeneous D

  .my-iso : (F G : Functor C D) (F≡G : F ≡F G) (G≡F : G ≡F F) (x : C.Obj) → D [ D [ oneway F G F≡G © x ∘ oneway G F G≡F © x ] ≡ D.id ]
  my-iso F G F≡G G≡F x = func (F.F₀ x) (G.F₀ x) (domain-≣ (F≡G (C.id {x}))) (domain-≣ (G≡F (C.id {x})))
    where
    module F = Functor F
    module G = Functor G
    -- hand-written function that "with" cannot properly abstract on its own, it gets itself all confused.
    func : (w z : D.Obj) (zz : w ≣ z ) (ww : z ≣ w) →
        ≣-subst (D._⇒_ w) zz (D.id {w}) D.∘ ≣-subst (D._⇒_ z) ww (D.id {z}) D.≡ D.id
    func w .w ≣-refl ≣-refl = D.identityʳ
