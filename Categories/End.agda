open import Categories.Category

module Categories.End {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {V : Category o′ ℓ′ e′} where
private
  module C = Category C
  module V = Category V
open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.DinaturalTransformation
open import Categories.Functor.Constant
open import Level
open import Categories.Morphisms V
open import Categories.Square
open import Data.Product

record End-data (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    E : V.Obj
    π : DinaturalTransformation {C = C} (Constant E) F

  module π = DinaturalTransformation π
  open π using (α)
  π∘_ : ∀ {Q} → Q V.⇒ E → End-data F
  π∘_ {Q} g = record { π = record { α = λ c → α c ∘ g; commute = λ {c c′} f → 
               begin
                  F.F₁ (f , C.id) ∘ ((α c′ ∘ g) ∘ id)
                ↓⟨ ∘-resp-≡ʳ identityʳ ⟩
                  F.F₁ (f , C.id) ∘ (α c′ ∘ g)
                ↑⟨ assoc ⟩
                  (F.F₁ (f , C.id) ∘ α c′) ∘ g
                ↑⟨ ∘-resp-≡ʳ identityˡ ⟩
                  (F.F₁ (f , C.id) ∘ α c′) ∘ (id ∘ g)
                ↑⟨ assoc ⟩
                  ((F.F₁ (f , C.id) ∘ α c′) ∘ id) ∘ g
                ↓⟨ ∘-resp-≡ˡ assoc ⟩
                  (F.F₁ (f , C.id) ∘ (α c′ ∘ id)) ∘ g
                ↓⟨ ∘-resp-≡ˡ (π.commute f) ⟩
                  (F.F₁ (C.id , f) ∘ (α c ∘ id)) ∘ g
                ↓⟨ assoc ⟩
                  F.F₁ (C.id , f) ∘ (α c ∘ id) ∘ g
                ↓⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ identityʳ) ⟩
                  F.F₁ (C.id , f) ∘ α c ∘ g
                ↑⟨ ∘-resp-≡ʳ identityʳ ⟩
                  F.F₁ (C.id , f) ∘ (α c ∘ g) ∘ id ∎
{-          begin
            F.F₁ (f , C.id) ∘ (α c′ ∘ g) ∘ ID ↓⟨ Equiv.refl ⟩
            (F.F₁ (f , C.id) ∙ α c′ ∙ ID) ∙ g ↓≡⟨ ∘-resp-≡ˡ (π.commute f) ⟩
            (F.F₁ (C.id , f) ∙ α c ∙ ID) ∙ g  ↓⟨ Equiv.refl ⟩
            F.F₁ (C.id , f) ∙ (α c ∙ g) ∙ ID  ∎ -} } }
   where
     -- open AUReasoning V
     open V.HomReasoning
     module F = Functor F
     open V

  .commute : ∀ {a b} (f : a C.⇒ b) -> Functor.F₁ F (f , C.id) V.∘ α b V.≡ Functor.F₁ F (C.id , f) V.∘ α a
  commute {c} {c′} f =  begin
            F.F₁ (f , C.id) ∘ α c′      ↑⟨ ∘-resp-≡ʳ identityʳ ⟩
            F.F₁ (f , C.id) ∘ α c′ ∘ id ↓⟨ π.commute f ⟩
            F.F₁ (C.id , f) ∘ α c  ∘ id ↓⟨ ∘-resp-≡ʳ identityʳ ⟩
            F.F₁ (C.id , f) ∘ α c       ∎ 
    where
      open V.HomReasoning
      module F = Functor F
      open V

open DinaturalTransformation using (α)


record End (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    Data : End-data F

  open End-data Data

  IsUni : (Q : End-data F) → (u : End-data.E Q V.⇒ E) → Set _
  IsUni Q u = ∀ c → α π c V.∘ u V.≡ α (End-data.π Q) c

  field
    universal : (Q : End-data F) → End-data.E Q V.⇒ E

    .π[c]∘universal≡δ[c] : {Q : End-data F} → IsUni Q (universal Q)

    .universal-unique : {Q : End-data F} → ∀ u → IsUni Q u → u V.≡ universal Q


  .eta-rule : universal Data V.≡ V.id
  eta-rule = begin universal Data ↑⟨ universal-unique {Data} V.id (λ c → V.identityʳ) ⟩
                   V.id           ∎
   where
    open V.HomReasoning

  .π-mono : ∀ {Q} (g₁ g₂ : Q V.⇒ E) → (∀ c → α π c V.∘ g₁ V.≡ α π c V.∘ g₂) → g₁ V.≡ g₂
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

endF : ∀ {o ℓ e} {A : Category o ℓ e}(F : Functor A (Functors (Product C.op C) V))
        → (∀ a → End (Functor.F₀ F a)) → Functor A V
endF {A = A} F mke = record {
                   F₀ = λ a → End.E (mke a);
                   F₁ = λ {a b} → F₁ {a} {b} ;
                   identity = λ {a} → V.Equiv.sym (End.universal-unique (mke a) V.id (λ c →
                     begin α (End.π (mke a)) c ∘ id                    ↓⟨ identityʳ ⟩
                           α (End.π (mke a)) c                         ↑⟨ identityˡ ⟩
                           id ∘ α (End.π (mke a)) c                    ↑⟨ ∘-resp-≡ˡ F.identity ⟩
                           η (F.F₁ A.id) (c , c) ∘ α (End.π (mke a)) c ∎ )) ;
                   homomorphism = λ {X Y Z f g} → V.Equiv.sym (End.universal-unique (mke Z) _ (λ c →
                       begin α (End.π (mke Z)) c ∘ F₁ g ∘ F₁ f
                                   ↑⟨ assoc ⟩
                             (α (End.π (mke Z)) c ∘ F₁ g) ∘ F₁ f
                                   ↓⟨ ∘-resp-≡ˡ (End.π[c]∘universal≡δ[c] (mke Z) {record {π = F.F₁ g <∘ End.π (mke Y)}} c) ⟩
                             (η (F.F₁ g) (c , c) ∘ α (End.π (mke Y)) c) ∘ F₁ f
                                   ↓⟨ assoc ⟩
                             η (F.F₁ g) (c , c) ∘ α (End.π (mke Y)) c ∘ F₁ f
                                   ↓⟨ ∘-resp-≡ʳ (End.π[c]∘universal≡δ[c] (mke Y) {record {π = F.F₁ f <∘ End.π (mke X)}} c) ⟩
                             η (F.F₁ g) (c , c) ∘ η (F.F₁ f) (c , c) ∘ α (End.π (mke X)) c
                                   ↑⟨ assoc ⟩
                             (η (F.F₁ g) (c , c) ∘ η (F.F₁ f) (c , c)) ∘ α (End.π (mke X)) c
                                   ↑⟨ ∘-resp-≡ˡ F.homomorphism  ⟩
                             η (F.F₁ (A [ g ∘ f ])) (c , c) ∘ α (End.π (mke X)) c
                                                                                   ∎ ));
                   F-resp-≡ = λ {a b f g} f≡g → End.universal-unique (mke b) _ (λ c → 
                          begin α (End.π (mke b)) c ∘ F₁ f               ↓⟨ End.π[c]∘universal≡δ[c] (mke b) c ⟩
                                η (F.F₁ f) (c , c) ∘ α (End.π (mke a)) c ↓⟨ ∘-resp-≡ˡ (F.F-resp-≡ f≡g) ⟩
                                η (F.F₁ g) (c , c) ∘ α (End.π (mke a)) c ∎ ) }
 where
  module A = Category A
  module F = Functor F
  open V
  open V.HomReasoning
  F₁ = λ {a b} f → End.universal (mke b) (record { E = _; π = (F.F₁ f) <∘ (End.π (mke a)) })
