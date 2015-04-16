{-# OPTIONS --universe-polymorphism #-}
module Categories.Globe where

import Level 
open import Relation.Binary using (IsEquivalence; module IsEquivalence)
open import Relation.Binary.PropositionalEquality using (isEquivalence)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<-trans)

open import Categories.Support.PropositionalEquality
open import Categories.Category

-- the stdlib doesn't have this
private
  ≤-unique : ∀ {m n} {x y : m ≤ n} → x ≣ y
  ≤-unique {x = z≤n} {z≤n} = ≣-refl
  ≤-unique {x = s≤s m≤n} {s≤s m≤n'} = ≣-cong s≤s ≤-unique

data GlobeHom : (m n : ℕ) → Set where
  I : {place : ℕ} → GlobeHom place place
  σ : {m n : ℕ} (n<m : n < m) → GlobeHom n m
  τ : {m n : ℕ} (n<m : n < m) → GlobeHom n m

infixl 7 _⊚_

_⊚_ : ∀ {l m n} → GlobeHom m n → GlobeHom l m → GlobeHom l n
I ⊚ y = y
x ⊚ I = x
σ n<m ⊚ σ m<l = σ (<-trans m<l n<m)
σ n<m ⊚ τ m<l = τ (<-trans m<l n<m)
τ n<m ⊚ σ m<l = σ (<-trans m<l n<m)
τ n<m ⊚ τ m<l = τ (<-trans m<l n<m)

Globe : Category Level.zero Level.zero Level.zero
Globe = record 
  { Obj = ℕ
  ; _⇒_ = GlobeHom
  ; _≡_ = _≣_
  ; id = I
  ; _∘_ = _⊚_
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc {f = f} {g} {h}
  ; identityˡ = λ {A} {B} {f} → ≣-refl
  ; identityʳ = identityʳ
  ; equiv = isEquivalence
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where

  assoc : ∀ {A B C D} {f : GlobeHom A B} {g : GlobeHom B C} {h : GlobeHom C D} → (h ⊚ g) ⊚ f ≣ h ⊚ (g ⊚ f)
  assoc {f = I} {I} {I} = ≣-refl
  assoc {f = I} {I} {σ _} = ≣-refl
  assoc {f = I} {I} {τ _} = ≣-refl
  assoc {f = I} {σ _} {I} = ≣-refl
  assoc {f = I} {σ _} {σ _} = ≣-refl
  assoc {f = I} {σ _} {τ _} = ≣-refl
  assoc {f = I} {τ _} {I} = ≣-refl
  assoc {f = I} {τ _} {σ _} = ≣-refl
  assoc {f = I} {τ _} {τ _} = ≣-refl
  assoc {f = σ _} {I} {I} = ≣-refl
  assoc {f = σ _} {I} {σ _} = ≣-refl
  assoc {f = σ _} {I} {τ _} = ≣-refl
  assoc {f = σ _} {σ _} {I} = ≣-refl
  assoc {f = σ _} {σ _} {σ _} = ≣-cong σ ≤-unique
  assoc {f = σ _} {σ _} {τ _} = ≣-cong σ ≤-unique
  assoc {f = σ _} {τ _} {I} = ≣-refl
  assoc {f = σ _} {τ _} {σ _} = ≣-cong σ ≤-unique
  assoc {f = σ _} {τ _} {τ _} = ≣-cong σ ≤-unique
  assoc {f = τ n<m} {I} {I} = ≣-refl
  assoc {f = τ n<m} {I} {σ _} = ≣-refl
  assoc {f = τ n<m} {I} {τ _} = ≣-refl
  assoc {f = τ n<m} {σ _} {I} = ≣-refl
  assoc {f = τ n<m} {σ _} {σ _} = ≣-cong τ ≤-unique
  assoc {f = τ n<m} {σ _} {τ _} = ≣-cong τ ≤-unique
  assoc {f = τ n<m} {τ _} {I} = ≣-refl
  assoc {f = τ n<m} {τ _} {σ _} = ≣-cong τ ≤-unique
  assoc {f = τ n<m} {τ _} {τ _} = ≣-cong τ ≤-unique

  -- this is necessary because Agda lies...
  identityʳ : ∀ {A B} {f : GlobeHom A B} → f ⊚ I ≣ f
  identityʳ {f = I} = ≣-refl
  identityʳ {f = σ _} = ≣-refl
  identityʳ {f = τ _} = ≣-refl

  ∘-resp-≡ : ∀ {A B C} {f h : GlobeHom B C} {g i : GlobeHom A B} → f ≣ h → g ≣ i → f ⊚ g ≣ h ⊚ i
  ∘-resp-≡ ≣-refl ≣-refl = ≣-refl

infixl 30 _σ′
infixl 30 _τ′

data GlobeHom′ : (m n : ℕ) → Set where
  I : ∀ {place : ℕ} → GlobeHom′ place place
  _σ′ : ∀ {n m : ℕ} → GlobeHom′ (suc n) m → GlobeHom′ n m
  _τ′ : ∀ {n m : ℕ} → GlobeHom′ (suc n) m → GlobeHom′ n m

data GlobeEq′ : {m n : ℕ} → GlobeHom′ m n → GlobeHom′ m n → Set where
  both-I : ∀ {m} → GlobeEq′ {m} {m} I I
  both-σ : ∀ {m n x y} → GlobeEq′ {m} {n} (x σ′) (y σ′)
  both-τ : ∀ {m n x y} → GlobeEq′ {m} {n} (x τ′) (y τ′)

GlobeEquiv : ∀ {m n} → IsEquivalence (GlobeEq′ {m} {n})
GlobeEquiv = record { refl = refl; sym = sym; trans = trans }
  where
  refl : ∀ {m n} {x : GlobeHom′ m n} → GlobeEq′ x x
  refl {x = I} = both-I
  refl {x = y σ′} = both-σ
  refl {x = y τ′} = both-τ
  sym : ∀ {m n} {x y : GlobeHom′ m n} → GlobeEq′ x y → GlobeEq′ y x
  sym both-I = both-I
  sym both-σ = both-σ
  sym both-τ = both-τ
  trans : ∀ {m n} {x y z : GlobeHom′ m n} → GlobeEq′ x y → GlobeEq′ y z → GlobeEq′ x z
  trans both-I y∼z = y∼z
  trans both-σ both-σ = both-σ
  trans both-τ both-τ = both-τ

infixl 7 _⊚′_

_⊚′_ : ∀ {l m n} → GlobeHom′ m n → GlobeHom′ l m → GlobeHom′ l n
x ⊚′ I = x
x ⊚′ y σ′ = (x ⊚′ y) σ′
x ⊚′ y τ′ = (x ⊚′ y) τ′

Globe′ : Category Level.zero Level.zero Level.zero
Globe′ = record 
  { Obj = ℕ
  ; _⇒_ = GlobeHom′
  ; _≡_ = GlobeEq′
  ; id = I
  ; _∘_ = _⊚′_
  ; assoc = λ {_ _ _ _ f g h} → assoc {f = f} {g} {h}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = GlobeEquiv
  ; ∘-resp-≡ = ∘-resp-≡
  }
  where
  assoc : ∀ {A B C D} {f : GlobeHom′ A B} {g : GlobeHom′ B C} {h : GlobeHom′ C D} → GlobeEq′ ((h ⊚′ g) ⊚′ f) (h ⊚′ (g ⊚′ f))
  assoc {f = I} = refl
    where open IsEquivalence GlobeEquiv
  assoc {f = y σ′} = both-σ
  assoc {f = y τ′} = both-τ
  identityˡ : ∀ {A B} {f : GlobeHom′ A B} → GlobeEq′ (I ⊚′ f) f
  identityˡ {f = I} = both-I
  identityˡ {f = y σ′} = both-σ
  identityˡ {f = y τ′} = both-τ
  identityʳ : ∀ {A B} {f : GlobeHom′ A B} → GlobeEq′ (f ⊚′ I) f
  identityʳ = IsEquivalence.refl GlobeEquiv
  ∘-resp-≡ : ∀ {A B C} {f h : GlobeHom′ B C} {g i : GlobeHom′ A B} → GlobeEq′ f h → GlobeEq′ g i → GlobeEq′ (f ⊚′ g) (h ⊚′ i)
  ∘-resp-≡ f∼h both-I = f∼h
  ∘-resp-≡ f∼h both-σ = both-σ
  ∘-resp-≡ f∼h both-τ = both-τ

-- Fix this
{-
data ReflexiveGlobeHom : (m n : ℕ) → Set where
  plain : ∀ {m n} → GlobeHom m n → ReflexiveGlobeHom m n
  ι : ∀ {m n} → ReflexiveGlobeHom m n → ReflexiveGlobeHom m (suc n)

stripped : ∀ {m n} → (cons : n < m → GlobeHom n m) → n < suc m → GlobeHom n m
stripped cons n<Sm with <-unsucʳ n<Sm
stripped cons n<Sm | inl ≣-refl = I
stripped cons n<Sm | inr n<m = cons n<m

_⊚ʳ_ : ∀ {l m n} → ReflexiveGlobeHom m n → ReflexiveGlobeHom l m → ReflexiveGlobeHom l n
ι x ⊚ʳ y = ι (x ⊚ʳ y)
plain x ⊚ʳ plain y = plain (x ⊚ y)
plain I ⊚ʳ ι y = ι y
plain (σ _) ⊚ʳ ι y = (plain (stripped σ n<m)) ⊚ʳ y
plain (τ n<m) ⊚ʳ ι y = (plain (stripped τ n<m)) ⊚ʳ y
-}
