{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.BinaryProducts

module Categories.Object.BinaryProducts.N-ary {o ℓ e}
  (C : Category o ℓ e)
  (BP : BinaryProducts C)
  where

open Category C
open BinaryProducts BP
open Equiv

import Categories.Object.Product
open Categories.Object.Product C

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec
open import Data.Product.N-ary hiding ([])

Prod : {n : ℕ} → Vec Obj (suc n) → Obj
Prod { zero} (A ∷ []) = A
Prod {suc n} (A ∷ As) = A × Prod {n} As

πˡ : {n m : ℕ}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → Prod (As ++ Bs) ⇒ Prod As
πˡ { zero} (A ∷ []) Bs = π₁
πˡ {suc n} (A ∷ As) Bs = ⟨ π₁ , πˡ {n} As Bs ∘ π₂ ⟩

πʳ : {n m : ℕ}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → Prod (As ++ Bs) ⇒ Prod Bs
πʳ { zero} (A ∷ []) Bs = π₂
πʳ {suc n} (A ∷ As) Bs = πʳ {n} As Bs ∘ π₂

glue : {n m : ℕ}{X : Obj}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → (f : X ⇒ Prod As)
  → (g : X ⇒ Prod Bs)
  → X ⇒ Prod (As ++ Bs)
glue { zero}{m} (A ∷ []) Bs f g = ⟨ f , g ⟩
glue {suc n}{m} (A ∷ As) Bs f g = ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩

open HomReasoning

.commuteˡ : {n m : ℕ}{X : Obj}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → πˡ As Bs ∘ glue As Bs f g ≡ f
commuteˡ { zero} (A ∷ []) Bs {f}{g} = commute₁
commuteˡ {suc n} (A ∷ As) Bs {f}{g} =
  begin
    ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
  ↓⟨ ⟨⟩∘ ⟩
    ⟨ π₁              ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
    , (πˡ As Bs ∘ π₂) ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
    ⟩
  ↓⟨ ⟨⟩-cong₂ commute₁ assoc ⟩
    ⟨ π₁ ∘ f
    , πˡ As Bs ∘ π₂ ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
    ⟩
  ↓⟨ ⟨⟩-congʳ (refl ⟩∘⟨ commute₂) ⟩
    ⟨ π₁ ∘ f , πˡ As Bs ∘ glue As Bs (π₂ ∘ f) g ⟩
  ↓⟨ ⟨⟩-congʳ (commuteˡ As Bs) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ f ⟩
  ↓⟨ g-η ⟩
    f
  ∎

.commuteʳ : {n m : ℕ}{X : Obj}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → πʳ As Bs ∘ glue As Bs f g ≡ g
commuteʳ { zero} (A ∷ []) Bs {f}{g} = commute₂
commuteʳ {suc n} (A ∷ As) Bs {f}{g} =
  begin
    (πʳ As Bs ∘ π₂) ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
  ↓⟨ assoc ⟩
    πʳ As Bs ∘ π₂ ∘ ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
  ↓⟨ refl ⟩∘⟨ commute₂ ⟩
    πʳ As Bs ∘ glue As Bs (π₂ ∘ f) g
  ↓⟨ commuteʳ As Bs ⟩
    g
  ∎

.N-universal : {n m : ℕ}{X : Obj}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → {h : X ⇒ Prod (As ++ Bs) }
  → πˡ As Bs ∘ h ≡ f
  → πʳ As Bs ∘ h ≡ g
  → glue As Bs f g ≡ h
N-universal { zero} (A ∷ []) Bs {f}{g}{h} h-commuteˡ h-commuteʳ = universal h-commuteˡ h-commuteʳ
N-universal {suc n} (A ∷ As) Bs {f}{g}{h} h-commuteˡ h-commuteʳ =
  begin
    ⟨ π₁ ∘ f , glue As Bs (π₂ ∘ f) g ⟩
  ↓⟨ ⟨⟩-congʳ (N-universal As Bs π₂∘h-commuteˡ π₂∘h-commuteʳ) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ h ⟩
  ↑⟨ ⟨⟩-congˡ π₁∘h-commuteˡ ⟩
    ⟨ π₁ ∘ h , π₂ ∘ h ⟩
  ↓⟨ g-η ⟩
    h
  ∎
  where
    -- h-commuteˡ : ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩ ∘ h ≡ f
    -- h-commuteʳ : (πʳ As Bs ∘ π₂) ∘ h ≡ g

    π₁∘h-commuteˡ : π₁ ∘ h ≡ π₁ ∘ f
    π₁∘h-commuteˡ =
      begin
        π₁ ∘ h
      ↑⟨ commute₁ ⟩∘⟨ refl ⟩
        (π₁ ∘ ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩) ∘ h
      ↓⟨ assoc ⟩
        π₁ ∘ ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩ ∘ h
      ↓⟨ refl ⟩∘⟨ h-commuteˡ ⟩
        π₁ ∘ f
      ∎

    π₂∘h-commuteˡ :  πˡ As Bs ∘ π₂ ∘ h ≡ π₂ ∘ f
    π₂∘h-commuteˡ =
      begin
        πˡ As Bs ∘ π₂ ∘ h
      ↑⟨ assoc ⟩
        (πˡ As Bs ∘ π₂) ∘ h
      ↑⟨ commute₂ ⟩∘⟨ refl ⟩
        (π₂ ∘ ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩) ∘ h
      ↓⟨ assoc ⟩
        π₂ ∘ ⟨ π₁ , πˡ As Bs ∘ π₂ ⟩ ∘ h
      ↓⟨ refl ⟩∘⟨ h-commuteˡ ⟩
        π₂ ∘ f
      ∎

    π₂∘h-commuteʳ : πʳ As Bs ∘ π₂ ∘ h ≡ g
    π₂∘h-commuteʳ = trans (sym assoc) h-commuteʳ

isProduct : {n m : ℕ}
  → (As : Vec Obj (suc n))
  → (Bs : Vec Obj (suc m))
  → Product (Prod As) (Prod Bs)
isProduct {n}{m} As Bs = record
  { A×B   = Prod (As ++ Bs)
  ; π₁    = πˡ As Bs
  ; π₂    = πʳ As Bs
  ; ⟨_,_⟩ = glue As Bs
  ; commute₁ = commuteˡ As Bs
  ; commute₂ = commuteʳ As Bs
  ; universal = N-universal As Bs
  }
