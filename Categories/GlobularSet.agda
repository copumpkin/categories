{-# OPTIONS --universe-polymorphism #-}
module Categories.GlobularSet where

open import Level
open import Data.Unit

open import Categories.Support.PropositionalEquality
open import Categories.Category
open import Categories.Globe
open import Categories.Functor
open import Categories.Presheaf
open import Categories.Agda

record GlobularSet (o : Level) : Set (suc o) where
  field
    presheaf : Presheaf Globe (Sets o)

Trivial : GlobularSet zero
Trivial = record
  { presheaf = record 
    { F₀ = λ x → ⊤
    ; F₁ = λ x y → y
    ; identity = ≣-refl
    ; homomorphism = ≣-refl
    ; F-resp-≡ = λ x → ≣-refl
    }
  }

zeroCell : ∀ {ℓ} → GlobularSet ℓ → Set ℓ
zeroCell G = Functor.F₀ (GlobularSet.presheaf G) 0

{-
lift : ∀ {ℓ} → (G : GlobularSet ℓ) → (A : Set ℓ) → (f g : zeroCell G → A) → GlobularSet ℓ
lift {ℓ} G A f g = record 
  { presheaf = record 
    { F₀ = F₀′
    ; F₁ = F₁′
    ; identity = ≣-refl
    ; homomorphism = {!!}
    ; F-resp-≡ = F-resp-≡′
    }
  }
  where
  open GlobularSet G
  open Functor presheaf

  F₀′ : ℕ → Set ℓ
  F₀′ zero = A
  F₀′ (suc n) = F₀ n

  F₁′ : ∀ {A B} → GlobeHom B A → F₀′ A → F₀′ B
  F₁′ I a = a
  F₁′ {suc zero} (σ Z<Sn) a = f a
  F₁′ {suc (suc m)} (σ Z<Sn) a = F₁′ {suc m} (σ Z<Sn) {!!}
  F₁′ (σ (raise< n<m)) a = {!!}
  F₁′ (τ n<m) a = {!!}

  F-resp-≡′ : ∀ {A B} {F G : GlobeHom B A} → F ≣ G → {x : F₀′ A} → F₁′ F x ≣ F₁′ G x
  F-resp-≡′ ≣-refl = ≣-refl


{-
objs : ∀ {ℓ} → (A : Set ℓ) → ℕ → Set ℓ
objs A zero = A
objs A (suc n) = Σ (objs A n) (λ x → Σ (objs A n) (λ y → x ≣ y))

base : ∀ {n} {ℓ} {A : Set ℓ} → objs A n → A
base {zero} o = o
base {suc n} (s , t , s≡t) = base {n} s 

homs : ∀ {A B} {ℓ} (Q : Set ℓ) → GlobeHom B A → objs Q A → objs Q B
homs Q I o = o
homs {suc n} Q (σ Z<Sn) (s , t , s≡t) = base {n} s
homs Q (σ (raise< n<m)) (s , .s , ≣-refl) = homs Q (σ n<m) s , homs Q (σ n<m) s , ≣-refl
homs {suc n} Q (τ Z<Sn) (s , t , s≡t) = base {n} t
homs Q (τ (raise< n<m)) (s , .s , ≣-refl) = homs Q (τ n<m) s , homs Q (τ n<m) s , ≣-refl

Equality : ∀ {ℓ} (A : Set ℓ) → GlobularSet ℓ
Equality A = record 
  { presheaf = record 
    { F₀ = objs A
    ; F₁ = homs A
    ; identity = ≣-refl
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism {f = f} {g}
    ; F-resp-≡ = F-resp-≡
    }
  }
  where
  homomorphism : {X Y Z : ℕ} {f : GlobeHom Y X} {g : GlobeHom Z Y} {x : objs A X} → homs A (f ⊚ g) x ≣ homs A g (homs A f x)
  homomorphism {f = I} = ≣-refl
  homomorphism {f = σ n<m} {I} = ≣-refl
  homomorphism {f = σ n<m} {σ n<m'} = {!!}
  homomorphism {f = σ n<m} {τ n<m'} = {!!}
  homomorphism {f = τ n<m} {I} = ≣-refl
  homomorphism {f = τ n<m} {σ n<m'} = {!!}
  homomorphism {f = τ n<m} {τ n<m'} = {!!}

  F-resp-≡ : {A' B : ℕ} {F G : GlobeHom B A'} → F ≣ G → {x : objs A A'} → _
  F-resp-≡ ≣-refl = ≣-refl
-}
-}