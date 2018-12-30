{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Object.Products

module Categories.Object.Products.N-ary {o ℓ e}
  (C : Category o ℓ e) 
  (P : Products C)
  where

open Category C
open Products P
open Equiv

import Categories.Object.Product
open Categories.Object.Product C

import Categories.Object.BinaryProducts
open Categories.Object.BinaryProducts C

import Categories.Object.BinaryProducts.N-ary

import Categories.Object.Terminal
open Categories.Object.Terminal C

open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product.N-ary hiding ([])

import Level

open import Relation.Binary.PropositionalEquality as PropEq
  using ()
  renaming (_≡_ to _≣_
           ; refl to ≣-refl
           ; sym  to ≣-sym
           ; cong to ≣-cong
           )

open BinaryProducts binary
module NonEmpty = Categories.Object.BinaryProducts.N-ary C binary
open Terminal terminal

Prod : {n : ℕ} → Vec Obj n → Obj
Prod { zero} [] = ⊤
Prod {suc n} As = NonEmpty.Prod As

-- This whole module is made a great deal more heinous than it should be
-- by the fact that "xs ++ [] ≣ xs" is ill-typed, so I have to repeatedly
-- prove trivial corrolaries of that fact without using it directly.
-- I don't really know how to deal with that in a sane way.

πˡ : {n m : ℕ}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → Prod (As ++ Bs) ⇒ Prod As
πˡ {       zero}      []       Bs  = !
πˡ {      suc n} (A ∷ As) (B ∷ Bs) = NonEmpty.πˡ (A ∷ As) (B ∷ Bs)
πˡ {   suc zero} (A ∷ [])      []  = id
πˡ {suc (suc n)} (A ∷ As)      []  = ⟨ π₁ , πˡ As [] ∘ π₂ ⟩

πʳ : {n m : ℕ}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → Prod (As ++ Bs) ⇒ Prod Bs
πʳ [] Bs = id
πʳ (A ∷ As) (B ∷ Bs) = NonEmpty.πʳ (A ∷ As) (B ∷ Bs)
πʳ As [] = !

glue : {n m : ℕ}{X : Obj}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → (f : X ⇒ Prod As)
  → (g : X ⇒ Prod Bs)
  → X ⇒ Prod (As ++ Bs)
glue {       zero}      []       Bs  f g = g
glue {      suc n} (A ∷ As) (B ∷ Bs) f g = NonEmpty.glue (A ∷ As) (B ∷ Bs) f g
glue {   suc zero} (A ∷ [])      []  f g = f
glue {suc (suc n)} (A ∷ As)      []  f g = ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩

open HomReasoning

.commuteˡ : {n m : ℕ}{X : Obj}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → πˡ As Bs ∘ glue As Bs f g ≡ f
commuteˡ {       zero}      []       Bs  {f}{g} = !-unique₂ (! ∘ g) f
commuteˡ {      suc n} (A ∷ As) (B ∷ Bs) {f}{g} = NonEmpty.commuteˡ (A ∷ As) (B ∷ Bs)
commuteˡ {   suc zero} (A ∷ [])      []  {f}{g} = identityˡ
commuteˡ {suc (suc n)} (A ∷ As)      []  {f}{g} = 
  begin
    ⟨ π₁ , πˡ As [] ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
  ↓⟨ ⟨⟩∘ ⟩
    ⟨ π₁              ∘ ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
    , (πˡ As [] ∘ π₂) ∘ ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
    ⟩ 
  ↓⟨ ⟨⟩-congʳ assoc ⟩
    ⟨ π₁            ∘ ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
    , πˡ As [] ∘ π₂ ∘ ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
    ⟩ 
  ↓⟨ ⟨⟩-cong₂ commute₁ (∘-resp-≡ʳ commute₂) ⟩
    ⟨ π₁ ∘ f , πˡ As [] ∘ glue As [] (π₂ ∘ f) g ⟩ 
  ↓⟨ ⟨⟩-congʳ (commuteˡ As []) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ f ⟩ 
  ↓⟨ g-η ⟩
      f
  ∎

.commuteʳ : {n m : ℕ}{X : Obj}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → πʳ As Bs ∘ glue As Bs f g ≡ g
commuteʳ {       zero}      []       Bs  {f}{g} = identityˡ
commuteʳ {      suc n} (A ∷ As) (B ∷ Bs) {f}{g} = NonEmpty.commuteʳ (A ∷ As) (B ∷ Bs)
commuteʳ {   suc zero} (A ∷ [])      []  {f}{g} = !-unique₂ (! ∘ f) g
commuteʳ {suc (suc n)} (A ∷ As)      []  {f}{g} = !-unique₂ (! ∘ glue (A ∷ As) [] f g) g

.N-universal : {n m : ℕ}{X : Obj}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
  → {f : X ⇒ Prod As}
  → {g : X ⇒ Prod Bs}
  → {h : X ⇒ Prod (As ++ Bs) }
  → πˡ As Bs ∘ h ≡ f 
  → πʳ As Bs ∘ h ≡ g 
  → glue As Bs f g ≡ h
N-universal {       zero}      []       Bs  {f}{g}{h} h-commuteˡ h-commuteʳ = trans (sym h-commuteʳ) identityˡ
N-universal {      suc n} (A ∷ As) (B ∷ Bs) {f}{g}{h} h-commuteˡ h-commuteʳ = NonEmpty.N-universal (A ∷ As) (B ∷ Bs) h-commuteˡ h-commuteʳ
N-universal {   suc zero} (A ∷ [])      []  {f}{g}{h} h-commuteˡ h-commuteʳ = trans (sym h-commuteˡ) identityˡ
N-universal {suc (suc n)} (A ∷ As)      []  {f}{g}{h} h-commuteˡ h-commuteʳ = 
  begin
    ⟨ π₁ ∘ f , glue As [] (π₂ ∘ f) g ⟩
  ↓⟨ ⟨⟩-congʳ (N-universal As [] π₂∘h-commuteˡ π₂∘h-commuteʳ) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ h ⟩
  ↑⟨ ⟨⟩-congˡ π₁∘h-commuteˡ ⟩
    ⟨ π₁ ∘ h , π₂ ∘ h ⟩
  ↓⟨ g-η ⟩
    h
  ∎

  where
    -- h-commuteˡ : ⟨ π₁ , πˡ As [] ∘ π₂ ⟩ ∘ h ≡ f 
    -- h-commuteʳ : (πʳ As [] ∘ π₂) ∘ h ≡ g 
    
    π₁∘h-commuteˡ : π₁ ∘ h ≡ π₁ ∘ f 
    π₁∘h-commuteˡ =
      begin
        π₁ ∘ h
      ↑⟨ commute₁ ⟩∘⟨ refl ⟩
        (π₁ ∘ ⟨ π₁ , πˡ As [] ∘ π₂ ⟩) ∘ h
      ↓⟨ assoc ⟩
        π₁ ∘ ⟨ π₁ , πˡ As [] ∘ π₂ ⟩ ∘ h
      ↓⟨ refl ⟩∘⟨ h-commuteˡ ⟩
        π₁ ∘ f
      ∎
    
    π₂∘h-commuteˡ :  πˡ As [] ∘ π₂ ∘ h ≡ π₂ ∘ f 
    π₂∘h-commuteˡ =
      begin
        πˡ As [] ∘ π₂ ∘ h
      ↑⟨ assoc ⟩
        (πˡ As [] ∘ π₂) ∘ h
      ↑⟨ commute₂ ⟩∘⟨ refl ⟩
        (π₂ ∘ ⟨ π₁ , πˡ As [] ∘ π₂ ⟩) ∘ h
      ↓⟨ assoc ⟩
        π₂ ∘ ⟨ π₁ , πˡ As [] ∘ π₂ ⟩ ∘ h
      ↓⟨ refl ⟩∘⟨ h-commuteˡ ⟩
        π₂ ∘ f
      ∎
    
    π₂∘h-commuteʳ : πʳ As [] ∘ π₂ ∘ h ≡ g 
    π₂∘h-commuteʳ = !-unique₂ (πʳ As [] ∘ π₂ ∘ h) g

isProduct : {n m : ℕ}
  → (As : Vec Obj n)
  → (Bs : Vec Obj m)
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
