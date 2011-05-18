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


widen-+ : (b : ℕ) → ∀ {a} (c : Fin a) → Fin (a + b)
widen-+ b zero = zero
widen-+ b (suc y) = suc (widen-+ b y)

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

_chops_ : (n : ℕ) → ∀ {m} (k : Fin (n + m)) → Either (Fin n) (Fin m)
0 chops k = inr k
suc n chops zero = inl zero
suc n chops suc k = left suc (n chops k)

rejoin-chops : (n m : ℕ) (k : Fin (n + m)) → either₀ (widen-+ m) (shift n) (n chops k) ≣ k
rejoin-chops zero _ _ = ≣-refl
rejoin-chops (suc _) _ zero = ≣-refl
rejoin-chops (suc n') m (suc k') with n' chops k' | rejoin-chops n' m k'
rejoin-chops (suc _) _ (suc ._) | inl _ | ≣-refl = ≣-refl
rejoin-chops (suc _) _ (suc ._) | inr _ | ≣-refl = ≣-refl

chop-widen-+ : (n m : ℕ) (k : Fin n) → n chops widen-+ m k ≣ inl k
chop-widen-+ zero _ ()
chop-widen-+ (suc n') _ zero = ≣-refl
chop-widen-+ (suc n') m (suc k') with n' chops widen-+ m k' | chop-widen-+ n' m k'
chop-widen-+ (suc n') m (suc ._) | inl k' | ≣-refl = ≣-refl
chop-widen-+ (suc n') m (suc _) | inr _ | ()

chop-shift : (n m : ℕ) (k : Fin m) → n chops shift n k ≣ inr k
chop-shift zero m k = ≣-refl
chop-shift (suc n') m k = ≣-cong (left suc) (chop-shift n' m k)

_cat₀_ : ∀ {ℓ} {n m} {A : Set ℓ} (f : Fin n → A) (g : Fin m → A) → Fin (n + m) → A
_cat₀_ {n = n} {m} f g i = either₀ f g (n chops i)

∙-dist-cat₀ : ∀ {ℓ ℓ′} {n m} {A : Set ℓ} {A′ : Set ℓ′} (f : Fin n → A) (g : Fin m → A) (h : A → A′) {i : Fin (n + m)} → (h ∙ (f cat₀ g)) i ≣ ((h ∙ f) cat₀ (h ∙ g)) i
∙-dist-cat₀ {n = n} {A′ = A′} f g h {i} = answer
  where
  open ≣-reasoning A′
  split-i = n chops i
  answer = begin 
      ((h ∙ (f cat₀ g)) i)
    ≈⟨ ≣-refl ⟩
      (h ((f cat₀ g) i))
    ≈⟨ ≣-cong h ≣-refl ⟩
      h (either₀ f g split-i)
    ≈⟨ ≣-refl ⟩
      (h ∙ either₀ f g) split-i
    ≈⟨ ∙-dist-either₀ f g h {split-i} ⟩ 
      either₀ (h ∙ f) (h ∙ g) split-i
    ≈⟨ ≣-refl ⟩
      ((h ∙ f) cat₀ (h ∙ g)) i
    ∎

_cat_ : ∀ {ℓ} {n m} {A : Fin n → Set ℓ} {B : Fin m → Set ℓ} (f : (i : Fin n) → A i) (g : (j : Fin m) → B j) → (k : Fin (n + m)) → (A cat₀ B) k
_cat_ {n = n} f g i = either f g (n chops i)

_cat′_ : ∀ {ℓ} {n m} {A : Fin (n + m) → Set ℓ} (f : (i : Fin n) → A (widen-+ m i)) (g : (j : Fin m) → A (shift n j)) → (k : Fin (n + m)) → A k
_cat′_ {n = n} {m = m} {A = T} f g k = ≣-subst T (rejoin-chops n m k) (either′ {A = T ∙ either₀ (widen-+ m) (shift n)} f g (n chops k))

_✂_ : ∀ {n} (m : Fin (suc n)) {ℓ} {A : Set ℓ} (f : Fin n → A) → (Fin (unbound m) → A) × (Fin (n lessen m) → A)
_✂_ {n = n} m f = f ∙ enlarge m , f ∙ (≣-subst Fin (lessen-is-subtraction₁ n m) ∙ shift (unbound m))

_✂₀′_ : (m : ℕ) → ∀ {ℓ} {A : Set ℓ} {n} (f : Fin (m + n) → A) → (Fin m → A) × (Fin n → A)
_✂₀′_ m {n = n} f = f ∙ widen-+ n , f ∙ shift m

_✂′_ : (m : ℕ) → ∀ {ℓ} {n} {A : Fin (m + n) → Set ℓ} (f : (k : Fin (m + n)) → A k) → uncurry₀ _×_ (⟨ (λ Aˡ → (i : Fin m) → Aˡ i) , (λ Aʳ → (j : Fin n) → Aʳ j) ⟩ (m ✂₀′ A))
_✂′_ m {n = n} f = f ∙ widen-+ n , f ∙ shift m
