module Support.Nat where

open import Support

data _<_ : (n m : ℕ) → Set where
  Z<Sn : {n : ℕ} → zero < suc n
  raise< : {n m : ℕ} (n<m : n < m) → suc n < suc m

_>_ : (m n : ℕ) → Set
_>_ = flip _<_

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

<-irref : ∀ {n} → ¬ (n < n)
<-irref (raise< n<m) = <-irref n<m

<-trans : ∀ {l m n} → (l < m) → (m < n) → (l < n)
<-trans Z<Sn (raise< n<m) = Z<Sn
<-trans (raise< n<m) (raise< n<m') = raise< (<-trans n<m n<m')

<-trans-assoc : ∀ {a b c d} → {a<b : a < b} {b<c : b < c} {c<d : c < d} → <-trans a<b (<-trans b<c c<d) ≣ <-trans (<-trans a<b b<c) c<d
<-trans-assoc {a<b = Z<Sn} {raise< b<c} {raise< c<d} = ≣-refl
<-trans-assoc {a<b = raise< a<b} {raise< b<c} {raise< c<d} = ≣-cong raise< <-trans-assoc

<-unsucʳ : ∀ {m n} → m < suc n → Either (m ≣ n) (m < n)
<-unsucʳ (Z<Sn {zero}) = inl ≣-refl
<-unsucʳ (Z<Sn {suc y}) = inr Z<Sn
<-unsucʳ (raise< {n} {zero} ())
<-unsucʳ (raise< {n} {suc y} n<m) = (≣-cong suc +++ raise<) (<-unsucʳ n<m)

<-unsucˡ : ∀ {m n} → suc m < n → m < n
<-unsucˡ (raise< {zero} Z<Pn) = Z<Sn
<-unsucˡ (raise< {suc y} Sy<Pn) = raise< (<-unsucˡ Sy<Pn)

<-sucˡ : ∀ {m n} → m < n → Either (suc m ≣ n) (suc m < n)
<-sucˡ (Z<Sn {zero}) = inl ≣-refl
<-sucˡ (Z<Sn {suc y}) = inr (raise< Z<Sn)
<-sucˡ (raise< n<m) = (≣-cong suc +++ raise<) (<-sucˡ n<m)

<-sucʳ : ∀ {m n} → m < n → m < suc n
<-sucʳ Z<Sn = Z<Sn
<-sucʳ (raise< Pm<Pn) = raise< (<-sucʳ Pm<Pn)
