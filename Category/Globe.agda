{-# OPTIONS --universe-polymorphism #-}
module Category.Globe where

open import Support
open import Support.Nat

data GlobeHom : (m n : ℕ) → Set where
  I : {place : ℕ} → GlobeHom place place
  σ : {m n : ℕ} (n<m : n < m) → GlobeHom m n
  τ : {m n : ℕ} (n<m : n < m) → GlobeHom m n

data ReflexiveGlobeHom : (m n : ℕ) → Set where
  plain : ∀ {m n} → GlobeHom m n → ReflexiveGlobeHom m n
  ι : ∀ {m n} → ReflexiveGlobeHom m n → ReflexiveGlobeHom m (suc n)

_⊚_ : ∀ {l m n} → GlobeHom m n → GlobeHom l m → GlobeHom l n
I ⊚ y = y
σ n<m ⊚ I = σ n<m
σ n<m ⊚ σ m<l = σ (<-trans n<m m<l)
σ n<m ⊚ τ m<l = σ (<-trans n<m m<l)
τ n<m ⊚ I = τ (n<m)
τ n<m ⊚ σ m<l = τ (<-trans n<m m<l)
τ n<m ⊚ τ m<l = τ (<-trans n<m m<l)

stripped : ∀ {m n} → (cons : n < m → GlobeHom m n) → n < suc m → GlobeHom m n
stripped cons n<Sm with <-unsucʳ n<Sm
stripped cons n<Sm | inl ≣-refl = I
stripped cons n<Sm | inr n<m = cons n<m

_⊚ʳ_ : ∀ {l m n} → ReflexiveGlobeHom m n → ReflexiveGlobeHom l m → ReflexiveGlobeHom l n
ι x ⊚ʳ y = ι (x ⊚ʳ y)
plain x ⊚ʳ plain y = plain (x ⊚ y)
plain I ⊚ʳ ι y = ι y
plain (σ n<m) ⊚ʳ ι y = (plain (stripped σ n<m)) ⊚ʳ y
plain (τ n<m) ⊚ʳ ι y = (plain (stripped τ n<m)) ⊚ʳ y

{- still needs the actual category records -}