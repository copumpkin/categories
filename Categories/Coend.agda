open import Categories.Category

module Categories.Coend {o a o′ a′} {C : Category o a} {V : Category o′ a′} where
private
  module C = Category C
  module V = Category V

open import Categories.Support.PropositionalEquality

open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.DinaturalTransformation
open import Categories.Functor.Constant
open import Level
open import Categories.Morphisms V
open import Categories.Square

record Coend-data (F : Bifunctor C.op C V) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    E : V.Obj
    π : DinaturalTransformation {C = C} F (Constant E)
  
  module π = DinaturalTransformation π
  open π using (α; commute)
  _∘π : ∀ {Q} → E V.⇒ Q → Coend-data F
  g ∘π = record
    { π = record
      { α = λ c → g ∘ α c
      ; commute = λ {c c′} f → 
        begin
          ID ∙ (g ∙ α c′) ∙ F.F₁ (C.id , f)
        ↑⟨ ≣-refl ⟩ 
          g ∙ (ID ∙ α c′ ∙ F.F₁ (C.id , f))
        ↓≡⟨ ∘-resp-≡ʳ (commute f) ⟩ 
          g ∙ (ID ∙ α c ∙ F.F₁ (f , C.id))
        ↓⟨ ≣-refl ⟩ 
          ID ∙ (g ∙ α c) ∙ F.F₁ (f , C.id)
        ∎
      }
    }
   where
     open AUReasoning V
     module F = Functor F
     open import Data.Product
     open V


open DinaturalTransformation using (α)


record Coend (F : Bifunctor C.op C V) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    Data : Coend-data F

  open Coend-data Data

  IsUni : (Q : Coend-data F) → (u : V [ E , Coend-data.E Q ]) → Set _
  IsUni Q u = ∀ c → (u) V.∘ (α π c) V.≡ (α (Coend-data.π Q) c)

  field
    universal : (Q : Coend-data F) → V [ E , Coend-data.E Q ]

    .universal∘π[c]≡δ[c] : {Q : Coend-data F} → IsUni Q (universal Q)

    .universal-unique : {Q : Coend-data F} → ∀ u → IsUni Q u → V [ u ≡ universal Q ]


  .eta-rule : universal Data V.≡ V.id
  eta-rule = begin universal Data ↑⟨ universal-unique {Data} V.id (λ c → V.identityˡ) ⟩ 
                   V.id           ∎
   where
    open V.HomReasoning

  .π-mono : ∀ {Q} (g₁ g₂ : E V.⇒ Q) → (∀ c → g₁ V.∘ α π c V.≡ g₂ V.∘ α π c) → g₁ V.≡ g₂
  π-mono {Q} g₁ g₂ g₁∘π≡g₂∘π = begin 
     g₁                ↓⟨ universal-unique {g₁ ∘π} g₁ (λ c → V.Equiv.refl) ⟩ 
     universal (g₁ ∘π) ↑⟨ universal-unique {g₁ ∘π} g₂ (λ c → V.Equiv.sym (g₁∘π≡g₂∘π c)) ⟩ 
     g₂                ∎
    where
     open V.HomReasoning

  open Coend-data Data public

open import Data.Product
open import Categories.Product
open import Categories.FunctorCategory
import Categories.NaturalTransformation as NT
open NT.NaturalTransformation using (η)

coendF : ∀ {o a} {A : Category o a} (F : Functor A (Functors (Product C.op C) V)) 
          → (∀ a → Coend (Functor.F₀ F a)) → Functor A V
coendF {A = A} F mke = record
  { F₀ = λ a → Coend.E (mke a)
  ; F₁ = λ {a b} → F₁ {b} {a}
  ; identity = λ {a} → V.Equiv.sym (Coend.universal-unique (mke a) V.id (λ c → 
               begin
                 id ∘ α (Coend.π (mke a)) c
               ↑⟨ id-comm ⟩
                 α (Coend.π (mke a)) c ∘ id
               ↑⟨ ∘-resp-≡ʳ (≣-cong (λ f → η f (c , c)) F.identity) ⟩
                 α (Coend.π (mke a)) c ∘ η (F.F₁ A.id) (c , c) 
               ∎))
  ; homomorphism = λ {X Y Z f g} → V.Equiv.sym (Coend.universal-unique (mke X) _ (λ c →
                   begin
                     (F₁ g ∘ F₁ f) ∘ α (Coend.π (mke X)) c
                   ↓⟨ pullʳ (Coend.universal∘π[c]≡δ[c] (mke X) c) ⟩
                     F₁ g ∘ α (Coend.π (mke Y)) c ∘ η (F.F₁ f) (c , c)
                   ↓⟨ pullˡ (Coend.universal∘π[c]≡δ[c] (mke Y) c) ⟩
                     (α (Coend.π (mke Z)) c ∘ η (F.F₁ g) (c , c)) ∘ η (F.F₁ f) (c , c)
                   ↑⟨ pushʳ (≣-cong (λ f → η f (c , c)) F.homomorphism) ⟩
                      α (Coend.π (mke Z)) c ∘ η (F.F₁ (A [ g ∘ f ])) (c , c)
                   ∎))
  }
  where
  module A = Category A
  module F = Functor F
  open V
  open V.HomReasoning
  open GlueSquares V
  F₁ = λ {a b} f → Coend.universal (mke b) (record { π = (Coend.π (mke a)) ∘> F.F₁ f })

