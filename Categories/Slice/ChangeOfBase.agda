open import Categories.Category

module Categories.Slice.ChangeOfBase {o a} (C : Category o a) where

open Category C
open import Categories.Pullback C
open import Categories.Slice C

open import Categories.Support.PropositionalEquality

open import Categories.Functor using (Functor; EasyFunctor; module EasyFunctor)
open import Categories.Square
import Categories.Adjunction as Adj
open Adj using (_⊣_)
open GlueSquares C

module BC1 {X Y} (f : X ⇒ Y) where
  Σ[_] : Functor (slice X) (slice Y)
  Σ[_] = record
    { F₀ = λ g → sliceobj (f ∘ SliceObj.arr g)
    ; F₁ = λ {A B} g → slicearr (pullʳ (Slice⇒.triangle g))
    ; identity = ≣-refl
    ; homomorphism = ≣-refl
    }

  Δᵉ[_][_] : (∀ {Z} (g : Z ⇒ Y) → Pullback f g)
           → EasyFunctor (slice Y) (sliceᵉ X) 
  Δᵉ[_][_] pb = record
    { F₀ = λ g → sliceobj (pb.p₁ (SliceObj.arr g))
    ; F₁ = λ { {sliceobj {A} a} {sliceobj {B} b} (slicearr {g} g-cm)
                  → slicearr {h = pb.universal b (pb.p₁ a) (g ∘ pb.p₂ a) (Equiv.trans (pb.commutes a) (pushˡ (Equiv.sym g-cm)))}
                             (pb.p₁∘universal≡q₁ b) }
    ; identity = λ { {sliceobj {A} a} → Equiv.sym (pb.universal-unique a id
                                                     identityʳ
                                                     id-comm) }
    ; homomorphism = λ { {sliceobj {A} a} {sliceobj {B} b} {sliceobj {C} c}
                          {slicearr {g} g-cm} {slicearr {h} h-cm}
                        → let open HomReasoning in Equiv.sym
                            (pb.universal-unique c
                              (  universal c (p₁ b) (h ∘ p₂ b) _
                               ∘ universal b (p₁ a) (g ∘ p₂ a) _)
                              (begin
                                 p₁ c ∘ universal c (p₁ b) _ _ ∘ _
                               ↓⟨ pullˡ (p₁∘universal≡q₁ c) ⟩
                                 p₁ b ∘ universal b (p₁ a) _ _
                               ↓⟨ p₁∘universal≡q₁ b ⟩
                                 p₁ a
                               ∎)
                              (begin
                                 p₂ c ∘ universal c _ (h ∘ p₂ b) _ ∘ _
                               ↓⟨ pullˡ (p₂∘universal≡q₂ c) ⟩
                                 (h ∘ p₂ b) ∘ universal b _ (g ∘ p₂ a) _
                               ↓⟨ extendˡ (p₂∘universal≡q₂ b) ⟩
                                 (h ∘ g) ∘ p₂ a
                               ∎))
                        }
    }
    where
    module pb {Z} g = Pullback (pb {Z} g)
    open pb

  Δ[_][_] : (∀ {Z} (g : Z ⇒ Y) → Pullback f g) → Functor (slice Y) (slice X) 
  Δ[_][_] pb = EasyFunctor.functor (Δᵉ[_][_] pb)

  -- Π[_] : Functor (slice X) (slice Y)
  -- Π[_] = {!!}

  Σ⊣Δ[_][_] : (pb : ∀ {Z} (g : Z ⇒ Y) → Pullback f g) → (Σ[_] ⊣ Δ[_][_] pb)
  Σ⊣Δ[_][_] pb = record
    { unit = record
      { η = λ { (sliceobj {A} a) → record
        { h = universal (f ∘ a) a id (Equiv.sym identityʳ)
        ; triangle = p₁∘universal≡q₁ (f ∘ a)
        } }
      ; commute = λ { {sliceobj {A} a} {sliceobj {B} b} (slicearr {g} g-cm)
                    → EasyCategory.promote (sliceᵉ X) _ _
                      (let open HomReasoning in begin
                        universal (f ∘ b) b id _ ∘ g
                      ↓⟨ universal-unique (f ∘ b) _
                           (begin
                              p₁ (f ∘ b) ∘ universal (f ∘ b) b id _ ∘ g
                            ↓⟨ pullˡ (p₁∘universal≡q₁ (f ∘ b)) ⟩
                              b ∘ g
                            ↓⟨ g-cm ⟩
                              a
                            ∎)
                           (begin
                              p₂ (f ∘ b) ∘ universal (f ∘ b) b id _ ∘ g
                            ↓⟨ pullˡ (p₂∘universal≡q₂ (f ∘ b)) ⟩
                              id ∘ g
                            ↓⟨ identityˡ ⟩
                              g
                            ∎) ⟩
                        universal (f ∘ b) a g (Equiv.sym (pullʳ g-cm))
                      ↑⟨ universal-unique (f ∘ b) _
                           (begin
                              p₁ (f ∘ b) ∘ universal (f ∘ b) (p₁ (f ∘ a)) (g ∘ p₂ (f ∘ a)) _ ∘ universal (f ∘ a) a id _
                            ↓⟨ pullˡ (p₁∘universal≡q₁ (f ∘ b)) ⟩
                              p₁ (f ∘ a) ∘ universal (f ∘ a) a id _
                            ↓⟨ p₁∘universal≡q₁ (f ∘ a) ⟩
                              a
                            ∎)
                           (begin
                              p₂ (f ∘ b) ∘ universal (f ∘ b) (p₁ (f ∘ a)) (g ∘ p₂ (f ∘ a)) _ ∘ universal (f ∘ a) a id _
                            ↓⟨ pullˡ (p₂∘universal≡q₂ (f ∘ b)) ⟩
                              (g ∘ p₂ (f ∘ a)) ∘ universal (f ∘ a) a id _
                            ↓⟨ cancelRight (p₂∘universal≡q₂ (f ∘ a)) ⟩
                              g 
                            ∎) ⟩
                        universal (f ∘ b) (p₁ (f ∘ a)) (g ∘ p₂ (f ∘ a)) _
                          ∘ universal (f ∘ a) a id _
                      ∎) }
      }
    ; counit = record
      { η = λ { (sliceobj {A} a) → record
        { h = p₂ a
        ; triangle = Equiv.sym (pb.commutes a)
        } }
      ; commute = λ { {sliceobj {A} a} {sliceobj {B} b} (slicearr {g} g-cm)
                    → EasyCategory.promote (sliceᵉ Y) _ _
                      (let open HomReasoning in begin
                         p₂ b ∘ universal b (p₁ a) (g ∘ p₂ a) _
                       ↓⟨ p₂∘universal≡q₂ b ⟩
                         g ∘ p₂ a
                       ∎) }
      }
    ; zig = EasyCategory.promote (sliceᵉ Y) _ _ (Equiv.sym (p₂∘universal≡q₂ _))
    ; zag = λ { {sliceobj {A} a}
              → EasyCategory.promote (sliceᵉ X) _ _
                (let a′ = f ∘ p₁ a in let open HomReasoning in begin
                   id
                 ↓⟨ universal-unique a id identityʳ identityʳ ⟩
                   universal a (p₁ a) (p₂ a) (pb.commutes a)
                 ↑⟨ universal-unique a _
                      (begin
                         p₁ a ∘ universal a (p₁ a′) (p₂ a ∘ p₂ a′) _ ∘ universal a′ (p₁ a) id _
                       ↓⟨ pullˡ (p₁∘universal≡q₁ a) ⟩
                         p₁ a′ ∘ universal a′ (p₁ a) id _
                       ↓⟨ p₁∘universal≡q₁ a′ ⟩
                         p₁ a
                       ∎)
                      (begin
                         p₂ a ∘ universal a (p₁ a′) (p₂ a ∘ p₂ a′) _ ∘ universal a′ (p₁ a) id _
                       ↓⟨ pullˡ (p₂∘universal≡q₂ a) ⟩
                         (p₂ a ∘ p₂ a′) ∘ universal a′ (p₁ a) id _
                       ↓⟨ cancelRight (p₂∘universal≡q₂ a′) ⟩
                         p₂ a
                       ∎) ⟩
                   universal a (p₁ a′) (p₂ a ∘ p₂ a′) _
                     ∘ universal a′ (p₁ a) id _
                 ∎) }
    }
    where
    module pb {Z} g = Pullback (pb {Z} g)
    open pb