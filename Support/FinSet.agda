{-# OPTIONS --universe-polymorphism #-}
module Support.FinSet where

open import Support
open import Support.Nat

unbound : ∀ {n} (m : Fin n) → ℕ
unbound zero = zero
unbound {suc n} (suc y) = suc (unbound {n} y)

.Fin-is-bounded : ∀ (n : ℕ) (m : Fin n) → (unbound m < n)
Fin-is-bounded .(suc n) (zero {n}) = Z<Sn
Fin-is-bounded .(suc n) (suc {n} y) = raise< (Fin-is-bounded n y)

enlarge : ∀ {a} (b : Fin (suc a)) (c : Fin (unbound b)) → Fin a
enlarge {zero} zero ()
enlarge {zero} (suc ()) c
enlarge {suc a′} zero ()
enlarge {suc a′} (suc b′) zero = zero
enlarge {suc a′} (suc b′) (suc c′) = suc (enlarge b′ c′)

widen-by : ∀ {a} {b} (a≤b : a < suc b) (c : Fin a) → Fin b
widen-by Z<Sn ()
widen-by (raise< Z<Sn) zero = zero
widen-by (raise< (raise< n<m)) zero = zero
widen-by (raise< Z<Sn) (suc ())
widen-by (raise< (raise< n<m)) (suc y') = suc (widen-by (raise< n<m) y')

shift : (a : ℕ) → ∀ {b} (c : Fin b) → Fin (a + b)
shift zero c = c
shift (suc y) c = suc (shift y c)

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

lessen-is-subtraction₁ : ∀ (n : ℕ) (m : Fin (suc n)) → (unbound m + (n lessen m)) ≣ n
lessen-is-subtraction₁ n zero = ≣-refl
lessen-is-subtraction₁ .0 (suc {zero} ())
lessen-is-subtraction₁ .(suc y) (suc {suc y} y') = ≣-cong suc (lessen-is-subtraction₁ y y')

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

_✂_ : ∀ {n} (m : Fin (suc n)) {ℓ} {A : Set ℓ} (f : Fin n → A) → (Fin (unbound m) → A) × (Fin (n lessen m) → A)
_✂_ {n = n} m f = f ∙ enlarge m , f ∙ (≣-subst Fin (lessen-is-subtraction₁ n m) ∙ shift (unbound m))

_✂′_ : (m : ℕ) → ∀ {ℓ} {A : Set ℓ} {n} (f : Fin (m + n) → A) → (Fin m → A) × (Fin n → A)
_✂′_ m {n = n} f = f ∙ widen-by (+-is-nondecreasingʳ m n) , f ∙ shift m