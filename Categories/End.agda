open import Categories.Category

module Categories.End {o a o′ a′} {C : Category o a} {V : Category o′ a′} where
private
  module C = Category C
  module V = Category V

open import Categories.Support.PropositionalEquality
open import Categories.Operations

open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.DinaturalTransformation
open import Categories.Functor.Constant
open import Level
open import Categories.Morphisms V

record End-data (F : Bifunctor C.op C V) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    E : V.Obj
    π : DinaturalTransformation {C = C} (Constant E) F
  
  open DinaturalTransformation π using (α; commute)
  π∘_ : ∀ {Q} → Q V.⇒ E → End-data F
  π∘ g = record { π = record { α = λ c → α c ∘ g; commute = λ {c c′} f → 
          begin
            F.F₁ (f , C.id) ∘ (α c′ ∘ g) ∘ id ↓⟨ Equiv.refl ⟩∘⟨ identityʳ ⟩
            F.F₁ (f , C.id) ∘ α c′ ∘ g ↑⟨ assoc ⟩
            (F.F₁ (f , C.id) ∘ α c′) ∘ g ↑⟨ (Equiv.refl ⟩∘⟨ identityʳ) ⟩∘⟨ Equiv.refl ⟩ 
            (F.F₁ (f , C.id) ∘ α c′ ∘ id) ∘ g ↓⟨ commute f ⟩∘⟨ Equiv.refl ⟩ 
            (F.F₁ (C.id , f) ∘ α c ∘ id) ∘ g ↓⟨ (Equiv.refl ⟩∘⟨ identityʳ) ⟩∘⟨ Equiv.refl ⟩ 
            (F.F₁ (C.id , f) ∘ α c) ∘ g ↓⟨ assoc ⟩ 
            F.F₁ (C.id , f) ∘ α c ∘ g ↑⟨ Equiv.refl ⟩∘⟨ identityʳ ⟩ 
            F.F₁ (C.id , f) ∘ (α c ∘ g) ∘ id ∎ } }
   where
     open V.HomReasoning
     module F = Functor F
     open import Data.Product
     open V


open DinaturalTransformation using (α)


record End (F : Bifunctor C.op C V) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  field
    Data : End-data F

  open End-data Data
  open V

  IsUni : (Q : End-data F) → (u : End-data.E Q V.⇒ E) → Set _
  IsUni Q u = ∀ c → (α π c) ∘ u ≡ α (End-data.π Q) c

  field
    universal : (Q : End-data F) → End-data.E Q ⇒ E

    .π[c]∘universal≡δ[c] : {Q : End-data F} → IsUni Q (universal Q)

    .universal-unique : {Q : End-data F} → ∀ u → IsUni Q u → u ≡ universal Q


  .eta-rule : universal Data ≡ V.id
  eta-rule = begin universal Data ↑⟨ universal-unique {Data} V.id (λ c → V.identityʳ) ⟩ 
                   V.id           ∎
   where
    open V.HomReasoning

  .π-mono : ∀ {Q} (g₁ g₂ : Q ⇒ E) → (∀ c → α π c ∘ g₁ ≡ α π c ∘ g₂) → g₁ ≡ g₂
  π-mono {Q} g₁ g₂ π∘g₁≡π∘g₂ = begin 
     g₁                ↓⟨ universal-unique {π∘ g₁} g₁ (λ c → V.Equiv.refl) ⟩ 
     universal (π∘ g₁) ↑⟨ universal-unique {π∘ g₁} g₂ (λ c → V.Equiv.sym (π∘g₁≡π∘g₂ c)) ⟩ 
     g₂                ∎
    where
     open V.HomReasoning

  open End-data Data public

open import Data.Product
open import Categories.Product
open import Categories.FunctorCategory
import Categories.NaturalTransformation as NT
open NT.NaturalTransformation using (η)

endF : ∀ {o a} {A : Category o a} (F : Functor A (Functors (Product C.op C) V)) 
        → (∀ a → End (Functor.F₀ F a)) → Functor A V
endF {A = A} F mke = record
  { F₀ = λ a → End.E (mke a)
  ; F₁ = λ {a b} → F₁ {a} {b}
  ; identity = λ {a} → V.Equiv.sym (End.universal-unique (mke a) V.id (λ c → 
               begin
                 α (End.π (mke a)) c ∘ id
               ↓⟨ identityʳ ⟩
                 α (End.π (mke a)) c
               ↑⟨ identityˡ ⟩
                 id ∘ α (End.π (mke a)) c
               ↑⟨ ≣-cong (λ f → η f (c , c)) F.identity ⟩∘⟨ Equiv.refl ⟩
                 η (F.F₁ A.id) (c , c) ∘ α (End.π (mke a)) c
               ∎))
  ; homomorphism = λ {X Y Z f g} → V.Equiv.sym (End.universal-unique (mke Z) _ (λ c →
                   begin
                     α (End.π (mke Z)) c ∘ F₁ g ∘ F₁ f
                   ↑⟨ assoc ⟩
                     (α (End.π (mke Z)) c ∘ F₁ g) ∘ F₁ f
                   ↓⟨ End.π[c]∘universal≡δ[c] (mke Z) c ⟩∘⟨ Equiv.refl ⟩
                     (η (F.F₁ g) (c , c) ∘ α (End.π (mke Y)) c) ∘ F₁ f
                   ↓⟨ assoc ⟩
                     η (F.F₁ g) (c , c) ∘ α (End.π (mke Y)) c ∘ F₁ f
                   ↓⟨ Equiv.refl ⟩∘⟨ End.π[c]∘universal≡δ[c] (mke Y) c ⟩
                     η (F.F₁ g) (c , c) ∘ η (F.F₁ f) (c , c) ∘ α (End.π (mke X)) c
                   ↑⟨ assoc ⟩
                     η (Functors (Product C.op C) V [ F.F₁ g ∘ F.F₁ f ]) (c , c) ∘ α (End.π (mke X)) c
                   ↑⟨ ≣-cong (λ f → η f (c , c)) F.homomorphism ⟩∘⟨ Equiv.refl ⟩
                     η (F.F₁ (A [ g ∘ f ])) (c , c) ∘ α (End.π (mke X)) c
                   ∎))
  }
  where
  module A = Category A
  module F = Functor F
  open V
  open V.HomReasoning
  F₁ = λ {a b} f → End.universal (mke b) (record { π = (F.F₁ f) <∘ (End.π (mke a)) })
