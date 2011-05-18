{-# OPTIONS --universe-polymorphism #-}
module Category.Globe where

open import Support
open import Support.Nat

open import Category

data GlobeHom : (m n : ℕ) → Set where
  I : {place : ℕ} → GlobeHom place place
  σ : {m n : ℕ} (n<m : n < m) → GlobeHom n m
  τ : {m n : ℕ} (n<m : n < m) → GlobeHom n m

_⊚_ : ∀ {l m n} → GlobeHom m n → GlobeHom l m → GlobeHom l n
I ⊚ y = y
x ⊚ I = x
σ n<m ⊚ σ m<l = σ (<-trans m<l n<m)
σ n<m ⊚ τ m<l = σ (<-trans m<l n<m)
τ n<m ⊚ σ m<l = τ (<-trans m<l n<m)
τ n<m ⊚ τ m<l = τ (<-trans m<l n<m)


Globe : Category zero zero zero
Globe = record 
  { Obj = ℕ
  ; _⇒_ = GlobeHom
  ; _≡_ = _≣_
  ; id = I
  ; _∘_ = _⊚_
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc {f = f} {g} {h}
  ; identityˡ = λ {A} {B} {f} → ≣-refl
  ; identityʳ = identityʳ
  ; equiv = ≣-is-equivalence (GlobeHom _ _)
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
  assoc {f = σ _} {σ _} {σ _} = ≣-cong σ <-trans-assoc
  assoc {f = σ _} {σ _} {τ _} = ≣-cong τ <-trans-assoc
  assoc {f = σ _} {τ _} {I} = ≣-refl
  assoc {f = σ _} {τ _} {σ _} = ≣-cong σ <-trans-assoc
  assoc {f = σ _} {τ _} {τ _} = ≣-cong τ <-trans-assoc
  assoc {f = τ n<m} {I} {I} = ≣-refl
  assoc {f = τ n<m} {I} {σ _} = ≣-refl
  assoc {f = τ n<m} {I} {τ _} = ≣-refl
  assoc {f = τ n<m} {σ _} {I} = ≣-refl
  assoc {f = τ n<m} {σ _} {σ _} = ≣-cong σ <-trans-assoc
  assoc {f = τ n<m} {σ _} {τ _} = ≣-cong τ <-trans-assoc
  assoc {f = τ n<m} {τ _} {I} = ≣-refl
  assoc {f = τ n<m} {τ _} {σ _} = ≣-cong σ <-trans-assoc
  assoc {f = τ n<m} {τ _} {τ _} = ≣-cong τ <-trans-assoc

  -- this is necessary because Agda lies...
  identityʳ : ∀ {A B} {f : GlobeHom A B} → f ⊚ I ≣ f
  identityʳ {f = I} = ≣-refl
  identityʳ {f = σ _} = ≣-refl
  identityʳ {f = τ _} = ≣-refl

  ∘-resp-≡ : ∀ {A B C} {f h : GlobeHom B C} {g i : GlobeHom A B} → f ≣ h → g ≣ i → f ⊚ g ≣ h ⊚ i
  ∘-resp-≡ ≣-refl ≣-refl = ≣-refl

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