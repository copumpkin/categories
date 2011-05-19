module Support.Nat where

open import Support

data _<_ : (n m : ℕ) → Set where
  Z<Sn : {n : ℕ} → zero < suc n
  raise< : {n m : ℕ} (n<m : n < m) → suc n < suc m

infix 5 _>_
_>_ : (m n : ℕ) → Set
_>_ = flip _<_

infixr 7 _+_
_+_ : (n m : ℕ) → ℕ
zero + m = m
suc n + m = suc (n + m)

infixr 9 _*_
_*_ : (n m : ℕ) → ℕ
zero * m = zero
(suc n) * m = m + n * m

+-is-nondecreasingʳ : ∀ (n m : ℕ) → n < suc (n + m)
+-is-nondecreasingʳ zero m = Z<Sn
+-is-nondecreasingʳ (suc y) m = raise< (+-is-nondecreasingʳ y m)

+-idˡ : ∀ a → 0 + a ≣ a
+-idˡ a = ≣-refl

+-idʳ : ∀ a → a + 0 ≣ a
+-idʳ zero = ≣-refl
+-idʳ (suc y) = ≣-cong suc (+-idʳ y)

+-assocˡ : ∀ a b c → (a + b) + c ≣ a + (b + c)
+-assocˡ zero b c = ≣-refl
+-assocˡ (suc a) b c = ≣-cong suc (+-assocˡ a b c)

+-assocʳ : ∀ a b c → a + (b + c) ≣ (a + b) + c
+-assocʳ zero b c = ≣-refl
+-assocʳ (suc a) b c = ≣-cong suc (+-assocʳ a b c)

+-sucˡ : ∀ a b → suc a + b ≣ suc (a + b)
+-sucˡ a b = ≣-refl

+-sucʳ : ∀ a b → a + suc b ≣ suc (a + b)
+-sucʳ zero b = ≣-refl
+-sucʳ (suc y) b = ≣-cong suc (+-sucʳ y b)

+-comm : ∀ a b → a + b ≣ b + a
+-comm a zero = +-idʳ a
+-comm a (suc y) = ≣-trans (≣-cong suc (+-comm a y)) (+-sucʳ a y)

*-killˡ : ∀ a → 0 * a ≣ 0
*-killˡ a = ≣-refl

*-killʳ : ∀ a → a * 0 ≣ 0
*-killʳ zero = ≣-refl
*-killʳ (suc y) = *-killʳ y

*-idˡ : ∀ a → 1 * a ≣ a
*-idˡ a = +-idʳ a

*-idʳ : ∀ a → a * 1 ≣ a
*-idʳ zero = ≣-refl
*-idʳ (suc y) = ≣-cong suc (*-idʳ y)

*-dist-+ˡ : ∀ a b c → a * (b + c) ≣ a * b + a * c
*-dist-+ˡ zero b c = ≣-refl
*-dist-+ˡ (suc y) b c =
  begin
    (b + c) + y * (b + c)
  ≈⟨ ≣-cong (_+_ (b + c)) (*-dist-+ˡ y b c) ⟩
    (b + c) + y * b + y * c
  ≈⟨ +-assocʳ (b + c) (y * b) (y * c) ⟩
    ((b + c) + y * b) + y * c
  ≈⟨ ≣-cong (λ x → (x + y * b) + y * c) (+-comm b c) ⟩
    ((c + b) + y * b) + y * c
  ≈⟨ ≣-cong (λ x → x + y * c) (+-assocˡ c b (y * b)) ⟩
    (c + b + y * b) + y * c
  ≈⟨ ≣-cong (λ x → x + y * c) (+-comm c (b + y * b)) ⟩
    ((b + y * b) + c) + y * c
  ≈⟨ +-assocˡ (b + y * b) c (y * c) ⟩ 
    (b + y * b) + c + y * c
  ∎
  where open ≣-reasoning ℕ

*-dist-+ʳ : ∀ a b c → (a + b) * c ≣ a * c + b * c
*-dist-+ʳ zero b c = ≣-refl
*-dist-+ʳ (suc y) b c = ≣-trans (+-assocʳ c (y * c) (b * c)) (≣-cong (_+_ c) (*-dist-+ʳ y b c))

*-assocˡ : ∀ a b c → (a * b) * c ≣ a * (b * c)
*-assocˡ zero b c = ≣-refl
*-assocˡ (suc y) b c = ≣-trans (≣-cong (_+_ (b * c)) (*-assocˡ y b c))
                         (*-dist-+ʳ b (y * b) c)

*-assocʳ : ∀ a b c → (a * b) * c ≣ a * (b * c)
*-assocʳ zero b c = ≣-refl
*-assocʳ (suc y) b c = ≣-trans (≣-cong (_+_ (b * c)) (*-assocʳ y b c))
                         (*-dist-+ʳ b (y * b) c)

*-sucˡ : ∀ a b → (suc a) * b ≣ b + a * b
*-sucˡ a b = ≣-refl

*-sucʳ : ∀ a b → a * (suc b) ≣ a + a * b
*-sucʳ zero b = ≣-refl
*-sucʳ (suc y) b = ≣-cong suc (
    begin
      b + y * suc b
    ≈⟨ ≣-cong (_+_ b) (*-sucʳ y b) ⟩
      b + y + y * b
    ≈⟨ +-assocʳ b y (y * b) ⟩
      (b + y) + y * b
    ≈⟨ ≣-cong (λ x → x + y * b) (+-comm b y) ⟩
      (y + b) + y * b
    ≈⟨ +-assocˡ y b (y * b) ⟩
      y + b + y * b
    ∎)
  where open ≣-reasoning ℕ

*-comm : ∀ a b → a * b ≣ b * a
*-comm a zero = *-killʳ a
*-comm a (suc y) = 
    begin
      a * suc y
    ≈⟨ *-sucʳ a y ⟩
      a + a * y
    ≈⟨ ≣-cong (_+_ a) (*-comm a y) ⟩
      a + y * a
    ∎
  where open ≣-reasoning ℕ
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
