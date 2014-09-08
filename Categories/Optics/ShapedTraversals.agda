open import Categories.Category
open import Categories.Monad.Cartesian
open import Categories.Pullback

module Categories.Optics.ShapedTraversals {o a} {C : Category o a} (FC : FinitelyComplete C) (T : CartesianMonad C) where

open import Level

open import Categories.Adjunction using (module Adjunction)
open import Categories.Monad
open import Categories.Monad.Algebra
open import Categories.Monad.Kleisli
open import Categories.Slice
open import Categories.Slice.ChangeOfBase
open import Categories.Square

open Category C
open GlueSquares C
open FinitelyComplete C FC
open BC2 locallyCartesian

module T = CartesianMonad T
open T.F using () renaming (F₀ to T₀; F₁ to T₁)
open T using (μ[_])

module Kl = Category (Kleisli T.monad)

module Σ⊣Δ {X Y} (f : X ⇒ Y) = Adjunction (Σ⊣Δ[ f ])

module Setup {V S : Obj} (g : S ⇒ T₀ V) where
  open Pullback C (pullback (T₁ (! {V})) (T₁ ! ∘ g)) public using () renaming (P to ∇; p₁ to query; p₂ to rollback; commutes to T!∘query≡shape∘rollback; universal to <_,_∣_>; universal-unique to <>-unique; p₁∘universal≡q₁ to query∘<>≡q₁; p₂∘universal≡q₂ to rollback∘<>≡q₂)
  open Pullback C (pullback (T₁ (! {V})) (T₁ ! ∘ query)) public using () renaming (P to ∇₂; p₁ to query₂; p₂ to rollback₂; commutes to T!∘query₂≡shape₂∘rollback₂; universal to ₂<_,_∣_>₂; universal-unique to ₂<>₂-unique; p₁∘universal≡q₁ to query₂∘₂<>₂≡q₁; p₂∘universal≡q₂ to rollback₂∘₂<>₂≡q₂)

record Algebraic (V S : Obj) : Set (o ⊔ a) where
  constructor algebraic
  field
    get : S ⇒ T₀ V
  open Setup get public
  field
    putAlgebra : AlgebraOn (Σ⊣Δ.monad (T₁ (! {V}))) (sliceobj get)
  module putAlgebra = AlgebraOn _ putAlgebra
  open Slice⇒ C putAlgebra.action public renaming (h to put; triangle to put-get)
  open putAlgebra public using () renaming (identity to get-put; assoc to put-put)

{-
unnest : ∀ {S V} → Algebraic (T₀ V) S → Algebraic V S
unnest {S} {V} t = record
  { get = μ[ V ] ∘ t.get
  ; putAlgebra = record
    { action = record
      { h = {!PullbackSquare.universal (T.μ-equifibrant !) {!!} {!!} {!!}!}
      ; triangle = {!!}
      }
    ; assoc = {!!}
    ; identity = {!!}
    }
  }
  where
  module t = Algebraic t
-}

pulled : ∀ {P X Y} {p₁ : P ⇒ X} {p₂ : P ⇒ T₀ Y} {f : X ⇒ T₀ ⊤} (pb : PullbackSquare C p₁ p₂ f (T₁ !)) → Algebraic Y P
pulled {P} {X} {Y} {p₁} {p₂} {f} pb = record
  { get = p₂
  ; putAlgebra = record
    { action = record
      { h = put
      ; triangle = p₂∘universal≡q₂
      }
    ; assoc = EasyCategory.promote (sliceᵉ C _) _ _
        let open HomReasoning in
          begin
            put ∘ < query₂ , put ∘ rollback₂ ∣ _ >
          ↓⟨ universal-unique
              {commutes = begin
                 f ∘ p₁ ∘ rollback ∘ rollback₂
               ↓⟨ pullˡ commutes ⟩
                 (T₁ ! ∘ p₂) ∘ rollback ∘ rollback₂
               ↑⟨ pushˡ (T!∘query≡shape∘rollback) ⟩
                 (T₁ ! ∘ query) ∘ rollback₂
               ↑⟨ T!∘query₂≡shape₂∘rollback₂ ⟩
                 T₁ ! ∘ query₂
               ∎}
              _
              (begin
                 p₁ ∘ put ∘ < query₂ , put ∘ rollback₂ ∣ _ >
               ↓⟨ pullˡ p₁∘universal≡q₁ ⟩
                 (p₁ ∘ rollback) ∘ < query₂ , put ∘ rollback₂ ∣ _ >
               ↓⟨ pullʳ (rollback∘<>≡q₂) ⟩
                 p₁ ∘ (put ∘ rollback₂)
               ↓⟨ extendʳ p₁∘universal≡q₁ ⟩
                 p₁ ∘ rollback ∘ rollback₂
               ∎)
              (begin
                 p₂ ∘ put ∘ < query₂ , put ∘ rollback₂ ∣ _ >
               ↓⟨ pullˡ p₂∘universal≡q₂ ⟩
                 query ∘ < query₂ , put ∘ rollback₂ ∣ _ >
               ↓⟨ query∘<>≡q₁ ⟩
                 query₂
               ∎) ⟩
            universal (p₁ ∘ rollback ∘ rollback₂) query₂ _
          ↑⟨ universal-unique _ 
              (begin
                 p₁ ∘ put ∘ < query₂ , rollback ∘ rollback₂ ∣ _ >
               ↓⟨ pullˡ p₁∘universal≡q₁ ⟩
                 (p₁ ∘ rollback) ∘ < query₂ , rollback ∘ rollback₂ ∣ _ >
               ↓⟨ pullʳ (rollback∘<>≡q₂) ⟩
                 p₁ ∘ rollback ∘ rollback₂
               ∎)
              (begin
                 p₂ ∘ put ∘ < query₂ , rollback ∘ rollback₂ ∣ _ >
               ↓⟨ pullˡ p₂∘universal≡q₂ ⟩
                 query ∘ < query₂ , rollback ∘ rollback₂ ∣ _ >
               ↓⟨ query∘<>≡q₁ ⟩
                 query₂
               ∎) ⟩
            put ∘ < query₂ , rollback ∘ rollback₂ ∣ _ >
          ∎
    ; identity = EasyCategory.promote (sliceᵉ C _) _ _
        let open HomReasoning in
          begin
            put ∘ < p₂ , id ∣ _ >
          ↓⟨ universal-unique
              {commutes = Equiv.trans (∘-resp-≡ʳ identityʳ) commutes}
              (put ∘ < p₂ , id ∣ _ >)
              (begin
                 p₁ ∘ put ∘ < p₂ , id ∣ _ > 
               ↓⟨ pullˡ p₁∘universal≡q₁ ⟩
                 (p₁ ∘ rollback) ∘ < p₂ , id ∣ _ >
               ↓⟨ pullʳ rollback∘<>≡q₂ ⟩
                 p₁ ∘ id
               ∎)
              (begin
                 p₂ ∘ put ∘ < p₂ , id ∣ _ >
               ↓⟨ pullˡ p₂∘universal≡q₂ ⟩
                 query ∘ < p₂ , id ∣ _ >
               ↓⟨ query∘<>≡q₁ ⟩
                 p₂
               ∎) ⟩
            universal (p₁ ∘ id) p₂ _
          ↑⟨ universal-unique id Equiv.refl identityʳ ⟩
            id
          ∎
    }
  }
  where
  open PullbackSquare C pb
  open Setup (p₂)
  put : ∇ ⇒ P
  put = universal
          (p₁ ∘ rollback)
          query
          let open HomReasoning in begin
            f ∘ p₁ ∘ rollback
          ↓⟨ pullˡ (commutes) ⟩
            (T₁ ! ∘ p₂) ∘ rollback
          ↑⟨ T!∘query≡shape∘rollback ⟩
            T₁ ! ∘ query
          ∎

nested : ∀ {V} → Algebraic V (T₀ (T₀ V))
nested = pulled (T.μ-equifibrant _)

{- 
_Ⓣ_ : ∀ {S U V} → Algebraic U S → Algebraic V U → Algebraic V S
t₁ Ⓣ t₂ = record
  { get = t₂.g Kl.∘ t₁.g
  ; putAlgebra = record
    { action = record
      { h = {!t₁.p!}
      ; triangle = {!!}
      }
    ; assoc = {!!}
    ; identity = EasyCategory.promote (sliceᵉ C _) ((Σ⊣Δ.monad (T₁ !) C.∘ slicearr _)
                                                     (M.η[ Σ⊣Δ.monad (T₁ !) ] (sliceobj (t₂.g Kl.∘ t₁.g)))) (C.id (Σ⊣Δ.monad (T₁ !))) {!!}
    }
  }
  where
  module t₁ = Algebraic t₁ renaming (get to g; put to p)
  module t₂ = Algebraic t₂ renaming (get to g; put to p)
-}