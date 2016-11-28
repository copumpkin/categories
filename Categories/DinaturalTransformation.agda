{-# OPTIONS --universe-polymorphism #-}
module Categories.DinaturalTransformation where

open import Level
open import Data.Product

open import Categories.Category
import Categories.NaturalTransformation
private module NT = Categories.NaturalTransformation
open import Categories.Functor using (Functor) renaming (_∘_ to _∘F_)
open import Categories.Bifunctor using (Bifunctor; module Functor)
open import Categories.Product
open import Categories.Square

record DinaturalTransformation {o ℓ e o′ ℓ′ e′}
                               {C : Category o ℓ e}
                               {D : Category o′ ℓ′ e′}
                               (F G : Bifunctor (Category.op C) C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = Category C
    module D = Category D
  open Functor F renaming (op to Fop)
  open Functor G renaming (F₀ to G₀; F₁ to G₁; op to Gop)
  open D hiding (op)
  field
    α : (c : C.Obj) → D [ F₀ (c , c) , G₀ (c , c) ]

    .commute : ∀ {c c′} (f : C [ c , c′ ]) → G₁ (f , C.id) ∘ α c′ ∘ F₁ ( C.id , f ) ≡ G₁ ( C.id , f ) ∘ α c ∘ F₁ ( f , C.id )

  op : DinaturalTransformation {C = C.op} {D = D.op} Gop Fop
  op = record { α = α; commute = λ f → D.Equiv.trans assoc (D.Equiv.trans (D.Equiv.sym (commute f)) (D.Equiv.sym assoc)) }



_<∘_ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G H : Bifunctor (Category.op C) C D}
      → NT.NaturalTransformation G H → DinaturalTransformation {C = C} F G → DinaturalTransformation {C = C} F H
_<∘_ {C = C} {D} {F} {G} {H} eta alpha = record { α = λ c → η (c , c) ∘ α c; commute = λ {c} {c′} f → 
     begin
       H.F₁ (f , C.id) ∘ ((η (c′ , c′) ∘ α c′) ∘ F.F₁ (C.id , f))
     ↓⟨ ∘-resp-≡ʳ assoc ⟩
       H.F₁ (f , C.id) ∘ (η (c′ , c′) ∘ (α c′ ∘ F.F₁ (C.id , f)))
     ↑⟨ assoc ⟩
       (H.F₁ (f , C.id) ∘ η (c′ , c′)) ∘ (α c′ ∘ F.F₁ (C.id , f))
     ↑⟨ ∘-resp-≡ˡ (eta.commute (f , C.id)) ⟩
       (η (c , c′) ∘ G.F₁ (f , C.id)) ∘ (α c′ ∘ F.F₁ (C.id , f))
     ↓⟨ pullʳ (commute f) ⟩
       η (c , c′) ∘ G.F₁ (C.id , f) ∘ (α c ∘ F.F₁ (f , C.id))
     ↓⟨ pullˡ (eta.commute (C.id , f)) ⟩
       (H.F₁ (C.id , f) ∘ η (c , c)) ∘ (α c ∘ F.F₁ (f , C.id))
     ↓⟨ assoc ⟩
       H.F₁ (C.id , f) ∘ (η (c , c) ∘ (α c ∘ F.F₁ (f , C.id)))
     ↑⟨ ∘-resp-≡ʳ assoc ⟩
       H.F₁ (C.id , f) ∘ ((η (c , c) ∘ α c) ∘ F.F₁ (f , C.id))
     ∎
{-  This uses 'associative-unital reasoning, which is now broken.  Above uses
    direct reasoning, which is heavier, but works.  JC.
     begin
       H.F₁ (f , C.id) ∙ ((η (c′ , c′) ∙ α c′) ∙ F.F₁ (C.id , f))
     ↑⟨ refl ⟩
       (H.F₁ (f , C.id) ∙ η (c′ , c′)) ∙ (α c′ ∙ F.F₁ (C.id , f))
     ↑≡⟨ ∘-resp-≡ˡ (eta.commute (f , C.id)) ⟩
       (η (c , c′) ∙ G.F₁ (f , C.id)) ∙ (α c′ ∙ F.F₁ (C.id , f))
     ↓≡⟨ pullʳ (commute f) ⟩
       η (c , c′) ∙ G.F₁ (C.id , f) ∙ α c ∙ F.F₁ (f , C.id)
     ↓≡⟨ pullˡ (eta.commute (C.id , f)) ⟩
       (H.F₁ (C.id , f) ∙ η (c , c)) ∙ α c ∙ F.F₁ (f , C.id)
     ↓⟨ refl ⟩
       H.F₁ (C.id , f) ∙ (η (c , c) ∙ α c) ∙ F.F₁ (f , C.id)
     ∎ -} }
  where
    module C = Category C
    module D = Category D
    open D
    open D.Equiv
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module eta = NT.NaturalTransformation eta
    open eta using (η)
    open DinaturalTransformation alpha
    -- open AUReasoning D
    open HomReasoning
    open GlueSquares D

_∘>_ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G H : Bifunctor (Category.op C) C D}
       → DinaturalTransformation {C = C} G H → NT.NaturalTransformation F G → DinaturalTransformation {C = C} F H
alpha ∘> eta = DinaturalTransformation.op (eta.op <∘ alpha.op)
  where
    module eta = NT.NaturalTransformation eta
    module alpha = DinaturalTransformation alpha

_∘ʳ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Bifunctor (Category.op C) C D}
     → (η : DinaturalTransformation {C = C} F G) → (K : Functor E C) → DinaturalTransformation {C = E} (F ∘F ((Functor.op K) ⁂ K)) (G ∘F ((Functor.op K) ⁂ K))
_∘ʳ_ {C = C} {D = D} {E} {F} {G} η K = record
  { α = λ c → DinaturalTransformation.α η (K.F₀ c)
  ; commute = λ {c} {c′} f → begin
      G.F₁ (K.F₁ f , K.F₁ E.id) D.∘ η.α (K.F₀ c′) D.∘ F.F₁ (K.F₁ E.id , K.F₁ f)
        ↓⟨ G.F-resp-≡ (C.Equiv.refl , K.identity) ⟩∘⟨ D.Equiv.refl ⟩∘⟨ F.F-resp-≡ (K.identity , C.Equiv.refl) ⟩
      G.F₁ (K.F₁ f , C.id) D.∘ η.α (K.F₀ c′) D.∘ F.F₁ (C.id , K.F₁ f)
        ↓⟨ DinaturalTransformation.commute η (K.F₁ f) ⟩
      G.F₁ (C.id , K.F₁ f) D.∘ η.α (K.F₀ c) D.∘ F.F₁ (K.F₁ f , C.id)
        ↑⟨ G.F-resp-≡ (K.identity , C.Equiv.refl) ⟩∘⟨ D.Equiv.refl ⟩∘⟨ F.F-resp-≡ (C.Equiv.refl , K.identity) ⟩
      G.F₁ (K.F₁ E.id , K.F₁ f) D.∘ η.α (K.F₀ c) D.∘ F.F₁ (K.F₁ f , K.F₁ E.id)
        ∎
  }
  where
    module K = Functor K
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G
    module η = DinaturalTransformation η
    open D.HomReasoning
