{-# OPTIONS --universe-polymorphism #-}
module Categories.Square where

open import Categories.Category

module GlueSquares {o ℓ e} (C : Category o ℓ e) where
  private module C = Category C
  open C

  module Pulls {X Y Z} {a : Y ⇒ Z} {b : X ⇒ Y} {c : X ⇒ Z} (ab≡c : a ∘ b ≡ c) where
    .pullʳ : ∀ {W} {f : Z ⇒ W} → (f ∘ a) ∘ b ≡ f ∘ c
    pullʳ {f = f} =
      begin
        (f ∘ a) ∘ b
      ↓⟨ assoc ⟩
        f ∘ (a ∘ b)
      ↓⟨ ∘-resp-≡ʳ ab≡c ⟩
        f ∘ c
      ∎
      where open HomReasoning

    .pullˡ : ∀ {W} {f : W ⇒ X} → a ∘ (b ∘ f) ≡ c ∘ f
    pullˡ {f = f} =
      begin
        a ∘ (b ∘ f)
      ↑⟨ assoc ⟩
        (a ∘ b) ∘ f
      ↓⟨ ∘-resp-≡ˡ ab≡c ⟩
        c ∘ f
      ∎
      where open HomReasoning

  open Pulls public

  -- essentially composition in the arrow category
  .glue : {X Y Y′ Z Z′ W : Obj} {a : Z ⇒ W} {a′ : Y′ ⇒ Z′} {b : Y ⇒ Z} {b′ : X ⇒ Y′} {c : X ⇒ Y} {c′ : Y′ ⇒ Z} {c″ : Z′ ⇒ W} → CommutativeSquare c′ a′ a c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
  glue {a = a} {a′} {b} {b′} {c} {c′} {c″} sq-a sq-b = 
    begin
      (a ∘ b) ∘ c
    ↓⟨ pullʳ sq-b ⟩
      a ∘ (c′ ∘ b′)
    ↓⟨ pullˡ sq-a ⟩
      (c″ ∘ a′) ∘ b′
    ↓⟨ assoc ⟩
      c″ ∘ (a′ ∘ b′)
    ∎
    where
    open HomReasoning

  .glue◃◽ : {X Y Y′ Z W : Obj} {a : Z ⇒ W} {b : Y ⇒ Z} {b′ : X ⇒ Y′} {c : X ⇒ Y} {c′ : Y′ ⇒ Z} {c″ : Y′ ⇒ W} → a ∘ c′ ≡ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
  glue◃◽ {a = a} {b} {b′} {c} {c′} {c″} tri-a sq-b =
    begin
      (a ∘ b) ∘ c
    ↓⟨ pullʳ sq-b ⟩
      a ∘ (c′ ∘ b′)
    ↓⟨ pullˡ tri-a ⟩
      c″ ∘ b′
    ∎
    where
    open HomReasoning

  -- essentially composition in the over category
  .glueTrianglesʳ : ∀ {X X′ X″ Y} {a : X ⇒ Y} {b : X′ ⇒ X} {a′ : X′ ⇒ Y} {b′ : X″ ⇒ X′} {a″ : X″ ⇒ Y} 
    → a ∘ b ≡ a′ → a′ ∘ b′ ≡ a″ → a ∘ (b ∘ b′) ≡ a″
  glueTrianglesʳ {a = a} {b} {a′} {b′} {a″} a∘b≡a′ a′∘b′≡a″ =
    begin
      a ∘ (b ∘ b′)
    ↓⟨ pullˡ a∘b≡a′ ⟩
      a′ ∘ b′
    ↓⟨ a′∘b′≡a″ ⟩
      a″
    ∎
    where open HomReasoning

  -- essentially composition in the under category
  .glueTrianglesˡ : ∀ {X Y Y′ Y″} {b : X ⇒ Y} {a : Y ⇒ Y′} {b′ : X ⇒ Y′} {a′ : Y′ ⇒ Y″} {b″ : X ⇒ Y″} → a′ ∘ b′ ≡ b″ → a ∘ b ≡ b′ → (a′ ∘ a) ∘ b ≡ b″
  glueTrianglesˡ {b = b} {a} {b′} {a′} {b″} a′∘b′≡b″ a∘b≡b′ =
    begin
      (a′ ∘ a) ∘ b
    ↓⟨ pullʳ a∘b≡b′ ⟩
      a′ ∘ b′
    ↓⟨ a′∘b′≡b″ ⟩
      b″
    ∎
    where open HomReasoning

  module Cancellers {Y Y′ : Obj} {h : Y′ ⇒ Y} {i : Y ⇒ Y′} (inv : h ∘ i ≡ id) where

    .cancelRight : ∀ {Z} {f : Y ⇒ Z} → (f ∘ h) ∘ i ≡ f
    cancelRight {f = f} =
      begin
        (f ∘ h) ∘ i
      ↓⟨ pullʳ inv ⟩
        f ∘ id
      ↓⟨ identityʳ ⟩
        f
      ∎
      where open HomReasoning

    .cancelLeft : ∀ {X} {f : X ⇒ Y} → h ∘ (i ∘ f) ≡ f
    cancelLeft {f = f} =
      begin
        h ∘ (i ∘ f)
      ↓⟨ pullˡ inv ⟩
        id ∘ f
      ↓⟨ identityˡ ⟩
        f
      ∎
      where open HomReasoning

    .cancelInner : ∀ {X Z} {f : Y ⇒ Z} {g : X ⇒ Y} → (f ∘ h) ∘ (i ∘ g) ≡ f ∘ g
    cancelInner {f = f} {g} =
      begin
        (f ∘ h) ∘ (i ∘ g)
      ↓⟨ pullˡ cancelRight ⟩
        f ∘ g
      ∎
      where open HomReasoning
  
  open Cancellers public