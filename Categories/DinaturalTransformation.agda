{-# OPTIONS --universe-polymorphism #-}
module Categories.DinaturalTransformation where

open import Level
open import Data.Product

open import Categories.Category
import Categories.NaturalTransformation 
module NT = Categories.NaturalTransformation
open import Categories.Bifunctor using (Bifunctor; module Functor)
open import Categories.Square

record DinaturalTransformation {o a o′ a′}
                               {C : Category o a}
                               {D : Category o′ a′}
                               (F G : Bifunctor (Category.op C) C D) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
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



_<∘_ : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G H : Bifunctor (Category.op C) C D} 
      → NT.NaturalTransformation G H → DinaturalTransformation {C = C} F G → DinaturalTransformation {C = C} F H
_<∘_ {C = C} {D} {F} {G} {H} eta alpha = record { α = λ c → η (c , c) ∘ α c; commute = λ {c} {c′} f → 
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
     ∎ }
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
    open AUReasoning D
    open GlueSquares D

_∘>_ : ∀ {o a o′ a′} {C : Category o a} {D : Category o′ a′} {F G H : Bifunctor (Category.op C) C D} 
       → DinaturalTransformation {C = C} G H → NT.NaturalTransformation F G → DinaturalTransformation {C = C} F H
alpha ∘> eta = DinaturalTransformation.op (eta.op <∘ alpha.op)
  where
    module eta = NT.NaturalTransformation eta
    module alpha = DinaturalTransformation alpha
