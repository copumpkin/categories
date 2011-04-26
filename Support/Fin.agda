{-# OPTIONS --universe-polymorphism #-}
module Support.Fin where

open import Support
open import Support.Nat

unbound : ∀ {n} (m : Fin n) → ℕ
unbound zero = zero
unbound {suc n} (suc y) = suc (unbound {n} y)

.Fin-is-bounded : ∀ (n : ℕ) (m : Fin n) → (unbound m < n)
Fin-is-bounded .(suc n) (zero {n}) = Z<Sn
Fin-is-bounded .(suc n) (suc {n} y) = raise< (Fin-is-bounded n y)

_bounded-by_ : (m : ℕ) → ∀ {n} (m<n : m < n) → Fin n
.0 bounded-by Z<Sn = zero
.(suc n) bounded-by (raise< {n} n<m) = suc (n bounded-by n<m)

unbound-unbounds-bounded-by : ∀ (m n : ℕ) (m<n : m < n) → unbound (m bounded-by m<n) ≣ m
unbound-unbounds-bounded-by .0 .(suc n) (Z<Sn {n}) = ≣-refl
unbound-unbounds-bounded-by .(suc n) .(suc m) (raise< {n} {m} n<m) = ≣-cong suc (unbound-unbounds-bounded-by n m n<m)

_lessen_ : (n : ℕ) → (m : Fin (suc n)) → ℕ
n lessen zero = n
.0 lessen suc {zero} ()
.(suc y) lessen suc {suc y} y' = y lessen y'

.lessen-is-subtraction : ∀ (n : ℕ) (m : Fin (suc n)) → (unbound m + (n lessen m)) ≣ n
lessen-is-subtraction n zero = ≣-refl
lessen-is-subtraction .0 (suc {zero} ())
lessen-is-subtraction .(suc y) (suc {suc y} y') = ≣-cong suc (lessen-is-subtraction y y')

lessen-is-subtraction₂ : ∀ (n m : ℕ) → ((n + m) lessen (n bounded-by (+-is-nondecreasingʳ n m)) ≣ m)
lessen-is-subtraction₂ zero m = ≣-refl
lessen-is-subtraction₂ (suc y) m = lessen-is-subtraction₂ y m

_split_ : ∀ {n} (k : Fin n) (m : Fin (suc n)) → Either (Fin (unbound m)) (Fin (n lessen m))
k split zero = inr k
zero split suc y = inl zero
suc y split suc y' = left suc (y split y')

_cat_ : ∀ {ℓ} {n m} {A : Set ℓ} (f : Fin n → A) (g : Fin m → A) → Fin (n + m) → A
_cat_ {n = n} {m} f g i =
  either₀
    (f ∙ ≣-subst Fin (unbound-unbounds-bounded-by _ _ ndecr))
    (g ∙ ≣-subst Fin (lessen-is-subtraction₂ n m))
    (i split (n bounded-by ndecr))
  where
  ndecr = +-is-nondecreasingʳ n m
