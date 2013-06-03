{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Pullback {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

record Pullback {X Y Z}(f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    P  : Obj
    p₁ : P ⇒ X
    p₂ : P ⇒ Y

  field
    .commutes : f ∘ p₁ ≡ g ∘ p₂

    universal : ∀ {Q}(q₁ : Q ⇒ X)(q₂ : Q ⇒ Y)
              → .(commutes : (f ∘ q₁ ≡ g ∘ q₂)) → (Q ⇒ P)

    .universal-unique : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                        .{commutes : f ∘ q₁ ≡ g ∘ q₂}
                          (u : Q ⇒ P)
                          .(p₁∘u≡q₁ : p₁ ∘ u ≡ q₁)
                          .(p₂∘u≡q₂ : p₂ ∘ u ≡ q₂)
                      →   u ≡ universal q₁ q₂ commutes

    .p₁∘universal≡q₁  : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                          .{commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₁ ∘ universal q₁ q₂ commutes ≡ q₁)

    .p₂∘universal≡q₂  : ∀ {Q} {q₁ : Q ⇒ X} {q₂ : Q ⇒ Y}
                          .{commutes : f ∘ q₁ ≡ g ∘ q₂}
                      →   (p₂ ∘ universal q₁ q₂ commutes ≡ q₂)


glue : ∀ {W X Y Z : Obj} {f0 : W ⇒ X}{f : X ⇒ Z}{g : Y ⇒ Z}
         → (p : Pullback f g) → Pullback f0 (Pullback.p₁ p) → Pullback (f ∘ f0) g
glue {f0 = f0} {f} {g} R L = record {
                      P = L.P;
                      p₁ = L.p₁;
                      p₂ = R.p₂ ∘ L.p₂;
                      commutes = begin (f ∘ f0) ∘ L.p₁   ↓⟨ assoc ⟩ 
                                       f ∘ f0 ∘ L.p₁     ↓⟨ ∘-resp-≡ʳ L.commutes ⟩ 
                                       f ∘ R.p₁ ∘ L.p₂   ↑⟨ assoc ⟩ 
                                       (f ∘ R.p₁) ∘ L.p₂ ↓⟨ ∘-resp-≡ˡ R.commutes ⟩ 
                                       (g ∘ R.p₂) ∘ L.p₂ ↓⟨ assoc ⟩ 
                                       g ∘ R.p₂ ∘ L.p₂   ∎;
                      universal = λ q₁ q₂ commutes → L.universal q₁ (R.universal (f0 ∘ q₁) q₂ (Equiv.trans (Equiv.sym assoc) commutes)) 
                                                                    (Equiv.sym R.p₁∘universal≡q₁);
                      universal-unique = λ {Q} {q₁} u p₁∘u≡q₁ p₂∘u≡q₂ → 
                            L.universal-unique u p₁∘u≡q₁ 
                                       (R.universal-unique (L.p₂ ∘ u) (begin
                                                                         R.p₁ ∘ L.p₂ ∘ u   ↑⟨ assoc ⟩
                                                                         (R.p₁ ∘ L.p₂) ∘ u ↑⟨ ∘-resp-≡ˡ L.commutes ⟩
                                                                         (f0 ∘ L.p₁) ∘ u   ↓⟨ assoc ⟩
                                                                         f0 ∘ L.p₁ ∘ u     ↓⟨ ∘-resp-≡ʳ p₁∘u≡q₁ ⟩ 
                                                                         f0 ∘ q₁           ∎) 
                                                   (Equiv.trans (Equiv.sym assoc) p₂∘u≡q₂));
                      p₁∘universal≡q₁ = L.p₁∘universal≡q₁;
                      p₂∘universal≡q₂ = Equiv.trans assoc (Equiv.trans (∘-resp-≡ʳ L.p₂∘universal≡q₂) R.p₂∘universal≡q₂) } 
   where
    module L = Pullback L
    module R = Pullback R
    open HomReasoning
