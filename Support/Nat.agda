module Support.Nat where

open import Support

data _<_ : (n m : ℕ) → Set where
  Z<Sn : {n : ℕ} → zero < suc n
  raise< : {n m : ℕ} (n<m : n < m) → suc n < suc m

_+_ : (n m : ℕ) → ℕ
zero + m = m
suc n + m = suc (n + m)

+-is-nondecreasingʳ : ∀ (n m : ℕ) → n < suc (n + m)
+-is-nondecreasingʳ zero m = Z<Sn
+-is-nondecreasingʳ (suc y) m = raise< (+-is-nondecreasingʳ y m)

+-assocˡ : ∀ a b c → (a + b) + c ≣ a + (b + c)
+-assocˡ zero b c = ≣-refl
+-assocˡ (suc a) b c = ≣-cong suc (+-assocˡ a b c)

+-assocʳ : ∀ a b c → a + (b + c) ≣ (a + b) + c
+-assocʳ zero b c = ≣-refl
+-assocʳ (suc a) b c = ≣-cong suc (+-assocʳ a b c)

<-trans : ∀ {l m n} → (l < m) → (m < n) → (l < n)
<-trans Z<Sn (raise< n<m) = Z<Sn
<-trans (raise< n<m) (raise< n<m') = raise< (<-trans n<m n<m')

<-unsucʳ : ∀ {m n} → m < suc n → Either (m ≣ n) (m < n)
<-unsucʳ (Z<Sn {zero}) = inl ≣-refl
<-unsucʳ (Z<Sn {suc y}) = inr Z<Sn
<-unsucʳ (raise< {n} {zero} ())
<-unsucʳ (raise< {n} {suc y} n<m) = (≣-cong suc +++ raise<) (<-unsucʳ n<m)
