{-# OPTIONS --universe-polymorphism #-}
module Categories.Square where

open import Categories.Category

module GlueSquares {o ℓ e} (C : Category o ℓ e) where
  private module C = Category C
  open C

  .glue : {X Y Y′ Z Z′ W : Obj} {a : Z ⇒ W} {a′ : Y′ ⇒ Z′} {b : Y ⇒ Z} {b′ : X ⇒ Y′} {c : X ⇒ Y} {c′ : Y′ ⇒ Z} {c″ : Z′ ⇒ W} → CommutativeSquare c′ a′ a c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
  glue {a = a} {a′} {b} {b′} {c} {c′} {c″} sq-a sq-b = 
    begin
      (a ∘ b) ∘ c
    ↓⟨ assoc ⟩
      a ∘ b ∘ c
    ↓⟨ ∘-resp-≡ʳ sq-b ⟩
      a ∘ c′ ∘ b′
    ↑⟨ assoc ⟩
      (a ∘ c′) ∘ b′
    ↓⟨ ∘-resp-≡ˡ sq-a ⟩
      (c″ ∘ a′) ∘ b′
    ↓⟨ assoc ⟩
      c″ ∘ a′ ∘ b′
    ∎
    where
    open HomReasoning

  .glue◃◽ : {X Y Y′ Z W : Obj} {a : Z ⇒ W} {b : Y ⇒ Z} {b′ : X ⇒ Y′} {c : X ⇒ Y} {c′ : Y′ ⇒ Z} {c″ : Y′ ⇒ W} → a ∘ c′ ≡ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
  glue◃◽ {a = a} {b} {b′} {c} {c′} {c″} tri-a sq-b =
    begin
      (a ∘ b) ∘ c
    ↓⟨ assoc ⟩
      a ∘ (b ∘ c)
    ↓⟨ ∘-resp-≡ʳ sq-b ⟩
      a ∘ (c′ ∘ b′)
    ↑⟨ assoc ⟩
      (a ∘ c′) ∘ b′
    ↓⟨ ∘-resp-≡ˡ tri-a ⟩
      c″ ∘ b′
    ∎
    where
    open HomReasoning