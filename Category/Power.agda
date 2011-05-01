{-# OPTIONS --universe-polymorphism #-}
module Category.Power where

open import Support
open import Support.Nat
open import Support.FinSet
open import Category

Power : ∀ {o ℓ e} (C : Category o ℓ e) (n : ℕ) → Category o ℓ e
Power C n = record 
  { Obj = Fin n → Obj
  ; _⇒_ = λ x y → (m : Fin n) → (x m ⇒ y m)
  ; _≡_ = λ f g → (m : Fin n) → (f m ≡ g m)
  ; _∘_ = λ f g m → f m ∘ g m
  ; id = λ {x} m → id
  ; assoc = λ {A} {B} {C'} {D} {f} {g} {h} m → assoc
  ; identityˡ = λ {A} {B} {f} m → identityˡ
  ; identityʳ = λ {A} {B} {f} m → identityʳ
  ; equiv = record 
    { refl = λ {x} m → refl
    ; sym = λ f m → sym (f m)
    ; trans = λ f g m → trans (f m) (g m)
    }          
  ; ∘-resp-≡ = λ f≡g h≡i m → ∘-resp-≡ (f≡g m) (h≡i m)
  }
  where
  open Category.Category C
  open Equiv

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