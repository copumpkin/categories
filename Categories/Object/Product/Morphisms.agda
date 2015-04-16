-- Various operations and proofs on morphisms between products
{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Product.Morphisms {o ℓ e} (C : Category o ℓ e) where

import Categories.Object.Product
open Categories.Object.Product C

open Category C
open Equiv
open HomReasoning

open import Function using (flip)
open import Level

infix 10 [_]⟨_,_⟩ [_⇒_]_⁂_

[[_]] : ∀{A B} → Product A B → Obj
[[ p ]] = Product.A×B p

[_]⟨_,_⟩ : ∀ {A B C}
  → (p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
[ p ]⟨ f , g ⟩ = Product.⟨_,_⟩ p f g

[_]π₁ : ∀ {A B}
  → (p : Product A B) → [[ p ]] ⇒ A
[_]π₁ = Product.π₁

[_]π₂ : ∀ {A B}
  → (p : Product A B) → [[ p ]] ⇒ B
[_]π₂ = Product.π₂

[_⇒_]_⁂_ : ∀ {A B C D}
    → (p₁ : Product A C)
    → (p₂ : Product B D)
    → (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
[ p₁ ⇒ p₂ ] f ⁂ g = [ p₂ ]⟨ f ∘ p₁.π₁ , g ∘ p₁.π₂ ⟩
    where
        module p₁ = Product p₁
        module p₂ = Product p₂

.id⁂id : ∀ {A B}(p : Product A B) → [ p ⇒ p ] id ⁂ id ≡ id
id⁂id p =
  begin
    ⟨ id ∘ π₁ , id ∘ π₂ ⟩
  ↓⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
    ⟨ π₁ , π₂ ⟩
  ↓⟨ η ⟩
    id
  ∎
  where
  open Product p

.repack≡id⁂id : ∀{X Y}(p₁ p₂ : Product X Y) → repack p₁ p₂ ≡ [ p₁ ⇒ p₂ ] id ⁂ id
repack≡id⁂id p₁ p₂ = sym (Product.⟨⟩-cong₂ p₂ identityˡ identityˡ)
    where open Equiv

.[_⇒_]π₁∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} 
  → (p₁ : Product A C)
  → (p₂ : Product B D)
  → Product.π₁ p₂ ∘ [ p₁ ⇒ p₂ ] f ⁂ g ≡ f ∘ Product.π₁ p₁
[_⇒_]π₁∘⁂ {f = f} {g} p₁ p₂ = Product.commute₁ p₂

.[_⇒_]π₂∘⁂ : ∀ {A B C D} → {f : A ⇒ B} → {g : C ⇒ D} 
  → (p₁ : Product A C)
  → (p₂ : Product B D)
  → Product.π₂ p₂ ∘ [ p₁ ⇒ p₂ ] f ⁂ g ≡ g ∘ Product.π₂ p₁
[_⇒_]π₂∘⁂ {f = f} {g} p₁ p₂ = Product.commute₂ p₂

.[_⇒_]⁂-cong₂ : ∀ {A B C D}{f g h i}
    → (p₁ : Product A B)
    → (p₂ : Product C D)
    → f ≡ g
    → h ≡ i
    → [ p₁ ⇒ p₂ ] f ⁂ h ≡ [ p₁ ⇒ p₂ ] g ⁂ i
[_⇒_]⁂-cong₂ {A}{B}{C}{D}{f}{g}{h}{i} p₁ p₂ f≡g h≡i =
    Product.⟨⟩-cong₂ p₂ (∘-resp-≡ f≡g refl) (∘-resp-≡ h≡i refl)

.[_⇒_]⁂∘⟨⟩ : ∀{A B C D X}
  → {f  : A ⇒ C} {f′ : X ⇒ A}
  → {g  : B ⇒ D} {g′ : X ⇒ B}
  → (p₁ : Product A B)
  → (p₂ : Product C D)
  → ([ p₁ ⇒ p₂ ] f ⁂ g) ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≡ [ p₂ ]⟨ f ∘ f′ , g ∘ g′ ⟩
[_⇒_]⁂∘⟨⟩ {A}{B}{C}{D}{X}{f}{f′}{g}{g′} p₁ p₂ =
  begin
    [ p₂ ]⟨ f ∘ p₁.π₁ , g ∘ p₁.π₂ ⟩ ∘ [ p₁ ]⟨ f′ , g′ ⟩ 
  ↓⟨ p₂.⟨⟩∘ ⟩
    [ p₂ ]⟨ (f ∘ p₁.π₁) ∘ p₁.⟨_,_⟩ f′ g′ 
          , (g ∘ p₁.π₂) ∘ p₁.⟨_,_⟩ f′ g′ ⟩
  ↓⟨ p₂.⟨⟩-cong₂ assoc assoc ⟩
    [ p₂ ]⟨ f ∘ p₁.π₁ ∘ p₁.⟨_,_⟩ f′ g′ 
          , g ∘ p₁.π₂ ∘ p₁.⟨_,_⟩ f′ g′ ⟩
  ↓⟨ p₂.⟨⟩-cong₂ (∘-resp-≡ refl p₁.commute₁) (∘-resp-≡ refl p₁.commute₂) ⟩
    [ p₂ ]⟨ f ∘ f′ , g ∘ g′ ⟩
  ∎
  where
  module p₁ = Product p₁
  module p₂ = Product p₂


.[_⇒_⇒_]⁂∘⁂ : ∀ {A B C D E F}{f g h i}
    → (p₁ : Product A B)
    → (p₂ : Product C D)
    → (p₃ : Product E F)
    → ([ p₂ ⇒ p₃ ] g ⁂ i) ∘ ([ p₁ ⇒ p₂ ] f ⁂ h) ≡ [ p₁ ⇒ p₃ ] (g ∘ f) ⁂ (i ∘ h)
[_⇒_⇒_]⁂∘⁂ {A}{B}{C}{D}{E}{F}{f}{g}{h}{i} p₁ p₂ p₃ =
    begin
        [ p₃ ]⟨ g ∘ p₂.π₁ , i ∘ p₂.π₂ ⟩ ∘ [ p₂ ]⟨ f ∘ p₁.π₁ , h ∘ p₁.π₂ ⟩
    ↓⟨ [ p₂ ⇒ p₃ ]⁂∘⟨⟩ ⟩
        [ p₃ ]⟨ g ∘ f ∘ p₁.π₁ , i ∘ h ∘ p₁.π₂ ⟩
    ↑⟨ p₃.⟨⟩-cong₂ assoc assoc ⟩
        [ p₃ ]⟨ (g ∘ f) ∘ p₁.π₁ , (i ∘ h) ∘ p₁.π₂ ⟩
    ∎
    where
    module p₁ = Product p₁
    module p₂ = Product p₂
    module p₃ = Product p₃

.[_⇒_⇒_]repack∘⁂ : ∀ {A B C D}{f g}
    → (p₁ : Product A B)
    → (p₂ : Product C D)
    → (p₃ : Product C D)
    → repack p₂ p₃ ∘ [ p₁ ⇒ p₂ ] f ⁂ g ≡ [ p₁ ⇒ p₃ ] f ⁂ g
[_⇒_⇒_]repack∘⁂ {A}{B}{C}{D}{f}{g} p₁ p₂ p₃ =
  begin
    repack p₂ p₃ ∘ [ p₁ ⇒ p₂ ] f ⁂ g
  ↓⟨ repack≡id⁂id p₂ p₃ ⟩∘⟨ refl ⟩
    ([ p₂ ⇒ p₃ ] id ⁂ id) ∘ ([ p₁ ⇒ p₂ ] f ⁂ g)
  ↓⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]⁂∘⁂ ⟩
    [ p₁ ⇒ p₃ ] (id ∘ f) ⁂ (id ∘ g)
  ↓⟨ [ p₁ ⇒ p₃ ]⁂-cong₂ identityˡ identityˡ ⟩
    [ p₁ ⇒ p₃ ] f ⁂ g
  ∎

.[_⇒_⇒_]repack∘repack : ∀{A B} 
  → (p₁ p₂ p₃ : Product A B)
  → repack p₂ p₃ ∘ repack p₁ p₂ ≡ repack p₁ p₃
[_⇒_⇒_]repack∘repack = repack∘
{-
  begin
    repack p₂ p₃ ∘ repack p₁ p₂
  ↓⟨ repack≡id⁂id p₂ p₃ ⟩∘⟨ repack≡id⁂id p₁ p₂ ⟩
    ([ p₂ ⇒ p₃ ] id ⁂ id) ∘ ([ p₁ ⇒ p₂ ] id ⁂ id)
  ↓⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]⁂∘⁂ ⟩
    [ p₁ ⇒ p₃ ] (id ∘ id) ⁂ (id ∘ id)
  ↓⟨ [ p₁ ⇒ p₃ ]⁂-cong₂ identityˡ identityˡ ⟩
    [ p₁ ⇒ p₃ ] id ⁂ id
  ↑⟨ repack≡id⁂id p₁ p₃ ⟩
    repack p₁ p₃
  ∎
-}

[_⇒_]first 
    : ∀ {A B C}
    → (p₁ : Product A C) → (p₂ : Product B C)
    → A ⇒ B → [[ p₁ ]] ⇒ [[ p₂ ]]
[ p₁ ⇒ p₂ ]first f = [ p₁ ⇒ p₂ ] f ⁂ id

[_⇒_]second
    : ∀ {A B C}
    → (p₁ : Product A B) → (p₂ : Product A C)
    → B ⇒ C → [[ p₁ ]] ⇒ [[ p₂ ]]
[ p₁ ⇒ p₂ ]second g = [ p₁ ⇒ p₂ ] id ⁂ g

.first-id : ∀ {A B}(p : Product A B) → [ p ⇒ p ]first id ≡ id
first-id = id⁂id

.second-id : ∀ {A B}(p : Product A B) → [ p ⇒ p ]second id ≡ id
second-id = id⁂id

.[_⇒_]first∘⟨⟩ : ∀ {A B C D}
  → {f : B ⇒ C} {f′ : A ⇒ B} {g′ : A ⇒ D}
  → (p₁ : Product B D) (p₂ : Product C D)
  → [ p₁ ⇒ p₂ ]first f ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≡ [ p₂ ]⟨ f ∘ f′ , g′ ⟩
[_⇒_]first∘⟨⟩ {A}{B}{C}{D}{f}{f′}{g′} p₁ p₂ =
  begin
    [ p₁ ⇒ p₂ ]first f ∘ [ p₁ ]⟨ f′ , g′ ⟩
  ↓⟨ [ p₁ ⇒ p₂ ]⁂∘⟨⟩ ⟩
    [ p₂ ]⟨ f ∘ f′ , id ∘ g′ ⟩
  ↓⟨ p₂.⟨⟩-cong₂ refl identityˡ ⟩
    [ p₂ ]⟨ f ∘ f′ , g′ ⟩
  ∎
  where
  module p₂ = Product p₂

.[_⇒_]second∘⟨⟩ : ∀ {A B D E} 
  → {f′ : A ⇒ B} {g : D ⇒ E} {g′ : A ⇒ D} 
  → (p₁ : Product B D) (p₂ : Product B E)
  → [ p₁ ⇒ p₂ ]second g ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≡ [ p₂ ]⟨ f′ , g ∘ g′ ⟩
[_⇒_]second∘⟨⟩ {A}{B}{D}{E}{f′}{g}{g′} p₁ p₂ =
  begin
    [ p₁ ⇒ p₂ ]second g ∘ [ p₁ ]⟨ f′ , g′ ⟩
  ↓⟨ [ p₁ ⇒ p₂ ]⁂∘⟨⟩ ⟩
    [ p₂ ]⟨ id ∘ f′ , g ∘ g′ ⟩
  ↓⟨ p₂.⟨⟩-cong₂ identityˡ refl ⟩
    [ p₂ ]⟨ f′ , g ∘ g′ ⟩
  ∎
  where
  module p₂ = Product p₂

.[_⇒_⇒_]first∘first : ∀ {A B C D}{f : B ⇒ C} {g : A ⇒ B}
  → (p₁ : Product A D)
  → (p₂ : Product B D)
  → (p₃ : Product C D)
  → [ p₂ ⇒ p₃ ]first f ∘ [ p₁ ⇒ p₂ ]first g ≡ [ p₁ ⇒ p₃ ]first(f ∘ g)
[_⇒_⇒_]first∘first {A}{B}{C}{D}{f}{g} p₁ p₂ p₃ =
  begin
    [ p₂ ⇒ p₃ ]first f ∘ [ p₁ ⇒ p₂ ]first g
  ↓⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]⁂∘⁂ ⟩
    [ p₁ ⇒ p₃ ] (f ∘ g) ⁂ (id ∘ id)
  ↓⟨ [ p₁ ⇒ p₃ ]⁂-cong₂ refl identityˡ ⟩
    [ p₁ ⇒ p₃ ]first (f ∘ g)
  ∎

.[_⇒_⇒_]second∘second : ∀ {A B C D}{f : C ⇒ D} {g : B ⇒ C}
  → (p₁ : Product A B)
  → (p₂ : Product A C)
  → (p₃ : Product A D)
  → [ p₂ ⇒ p₃ ]second f ∘ [ p₁ ⇒ p₂ ]second g ≡ [ p₁ ⇒ p₃ ]second(f ∘ g)
[_⇒_⇒_]second∘second {A}{B}{C}{D}{f}{g} p₁ p₂ p₃ =
  begin
    [ p₂ ⇒ p₃ ]second f ∘ [ p₁ ⇒ p₂ ]second g
  ↓⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]⁂∘⁂ ⟩
    [ p₁ ⇒ p₃ ] (id ∘ id) ⁂ (f ∘ g)
  ↓⟨ [ p₁ ⇒ p₃ ]⁂-cong₂ identityˡ refl ⟩
    [ p₁ ⇒ p₃ ]second (f ∘ g)
  ∎

.[_⇒_,_⇒_]first↔second : ∀ {A B C D}{f : A ⇒ B}{g : C ⇒ D}
  → (p₁ : Product A D)
  → (p₂ : Product B D)
  → (p₃ : Product A C)
  → (p₄ : Product B C)
  → [ p₁ ⇒ p₂ ]first f ∘ [ p₃ ⇒ p₁ ]second g ≡ [ p₄ ⇒ p₂ ]second g ∘ [ p₃ ⇒ p₄ ]first f
[_⇒_,_⇒_]first↔second {A}{B}{C}{D}{f}{g} p₁ p₂ p₃ p₄ =
  begin
    [ p₁ ⇒ p₂ ]first f ∘ [ p₃ ⇒ p₁ ]second g
  ↓⟨ [ p₃ ⇒ p₁ ⇒ p₂ ]⁂∘⁂ ⟩
    [ p₃ ⇒ p₂ ] (f ∘ id) ⁂ (id ∘ g)
  ↓⟨ [ p₃ ⇒ p₂ ]⁂-cong₂ identityʳ identityˡ ⟩
    [ p₃ ⇒ p₂ ] f ⁂ g
  ↑⟨ [ p₃ ⇒ p₂ ]⁂-cong₂ identityˡ identityʳ ⟩
    [ p₃ ⇒ p₂ ] (id ∘ f) ⁂ (g ∘ id)
  ↑⟨ [ p₃ ⇒ p₄ ⇒ p₂ ]⁂∘⁂ ⟩
    [ p₄ ⇒ p₂ ]second g ∘ [ p₃ ⇒ p₄ ]first f
  ∎
