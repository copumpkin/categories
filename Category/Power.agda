{-# OPTIONS --universe-polymorphism #-}
module Category.Power where

open import Support
open import Support.Nat
open import Support.FinSet
open import Category

Power : ∀ {o ℓ e} (C : Category o ℓ e) (n : ℕ) → Category o ℓ e
Power C n = record 
  { Obj = Fin n → C.Obj
  ; Hom = λ x y → (m : Fin n) → C.Hom (x m) (y m)
  ; _≡_ = λ f g → (m : Fin n) → C._≡_ (f m) (g m)
  ; _∘_ = λ f g m → C._∘_ (f m) (g m)
  ; id = λ {x} m → C.id
  ; assoc = λ {A} {B} {C'} {D} {f} {g} {h} m → C.assoc
  ; identityˡ = λ {A} {B} {f} m → C.identityˡ
  ; identityʳ = λ {A} {B} {f} m → C.identityʳ
  ; equiv = record 
    { refl = λ {x} m → IsEquivalence.refl C.equiv
    ; sym = λ f m → IsEquivalence.sym C.equiv (f m)
    ; trans = λ f g m → IsEquivalence.trans C.equiv (f m) (g m)
    }          
  ; ∘-resp-≡ = λ f≡g h≡i m → C.∘-resp-≡ (f≡g m) (h≡i m)
  }
  where
  module C = Category.Category C

open import Category.Functor using (Functor)

Powerfunctor : ∀ {o ℓ e} (C : Category o ℓ e) (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Powerfunctor C n = Functor (Power C n) C

Hyperendo : ∀ {o ℓ e} (C : Category o ℓ e) (n m : ℕ) → Set (e ⊔ ℓ ⊔ o)
Hyperendo C n m = Functor (Power C n) (Power C m)

Polyendo : ∀ {o ℓ e} (C : Category o ℓ e) (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Polyendo C n = Hyperendo C n n

{-
_∥_ : ∀ {o ℓ e} {C : Category o ℓ e} {n n′ m m′} (F : Hyperendo C n n′) (G : Hyperendo C m m′) → Hyperendo C (n + m) (n′ + m′)
_∥_ {C = C} {n} {n′} {m} {m′} F G = record
  { F₀ = λ f → uncurry₀ _cat_ (⟨ Functor.F₀ F , Functor.F₀ G ⟩ (n ✂′ f))
  ; F₁ = λ x → uncurry₀ _cat_ (⟨ {!Functor.F₁ F!} , {!Functor.F₁ G!} ⟩ {!n ✂′ x!})
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ x → {!!}
  }
-}