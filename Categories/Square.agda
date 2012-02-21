{-# OPTIONS --universe-polymorphism #-}
module Categories.Square where

open import Categories.Category
import Categories.Morphisms as Mor

module GlueSquares {o a} (C : Category o a) where
  private module C = Category C
  open C
  open Mor C

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

  module Pushes {X Y Z} {a : Y ⇒ Z} {b : X ⇒ Y} {c : X ⇒ Z} (c≡ab : c ≡ a ∘ b) where
    .pushʳ : ∀ {W} {f : Z ⇒ W} → f ∘ c ≡ (f ∘ a) ∘ b
    pushʳ {f = f} =
      begin
        f ∘ c
      ↓⟨ ∘-resp-≡ʳ c≡ab ⟩
        f ∘ (a ∘ b)
      ↑⟨ assoc ⟩
        (f ∘ a) ∘ b
      ∎
      where open HomReasoning

    .pushˡ : ∀ {W} {f : W ⇒ X} → c ∘ f ≡ a ∘ (b ∘ f)
    pushˡ {f = f} =
      begin
        c ∘ f
      ↓⟨ ∘-resp-≡ˡ c≡ab ⟩
        (a ∘ b) ∘ f
      ↓⟨ assoc ⟩
        a ∘ (b ∘ f)
      ∎
      where open HomReasoning

  open Pushes public

  module IntroElim {X} {a : X ⇒ X} (a≡id : a ≡ id) where
    .elimʳ : ∀ {W} {f : X ⇒ W} → (f ∘ a) ≡ f
    elimʳ {f = f} =
      begin
        f ∘ a
      ↓⟨ ∘-resp-≡ʳ a≡id ⟩
        f ∘ id
      ↓⟨ identityʳ ⟩
        f
      ∎
      where
      open HomReasoning

    .introʳ : ∀ {W} {f : X ⇒ W} → f ≡ f ∘ a
    introʳ = Equiv.sym elimʳ

    .elimˡ : ∀ {W} {f : W ⇒ X} → (a ∘ f) ≡ f
    elimˡ {f = f} =
      begin
        a ∘ f
      ↓⟨ ∘-resp-≡ˡ a≡id ⟩
        id ∘ f
      ↓⟨ identityˡ ⟩
        f
      ∎
      where
      open HomReasoning

    .introˡ : ∀ {W} {f : W ⇒ X} → f ≡ a ∘ f
    introˡ = Equiv.sym elimˡ

  open IntroElim public

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

  module Switch {X Y} (i : X ≅ Y) where
    open _≅_ i

    .switch-fgˡ : ∀ {W} {h : W ⇒ X} {k : W ⇒ Y} → (f ∘ h ≡ k) → (h ≡ g ∘ k)
    switch-fgˡ {h = h} {k} pf =
      begin
        h
      ↑⟨ cancelLeft isoˡ ⟩
        g ∘ (f ∘ h)
      ↓⟨ ∘-resp-≡ʳ pf ⟩
        g ∘ k
      ∎
      where open HomReasoning

    .switch-gfˡ : ∀ {W} {h : W ⇒ Y} {k : W ⇒ X} → (g ∘ h ≡ k) → (h ≡ f ∘ k)
    switch-gfˡ {h = h} {k} pf =
      begin
        h
      ↑⟨ cancelLeft isoʳ ⟩
        f ∘ (g ∘ h)
      ↓⟨ ∘-resp-≡ʳ pf ⟩
        f ∘ k
      ∎
      where open HomReasoning

    .switch-fgʳ : ∀ {W} {h : Y ⇒ W} {k : X ⇒ W} → (h ∘ f ≡ k) → (h ≡ k ∘ g)
    switch-fgʳ {h = h} {k} pf =
      begin
        h
      ↑⟨ cancelRight isoʳ ⟩
        (h ∘ f) ∘ g
      ↓⟨ ∘-resp-≡ˡ pf ⟩
        k ∘ g
      ∎
      where open HomReasoning

    .switch-gfʳ : ∀ {W} {h : X ⇒ W} {k : Y ⇒ W} → (h ∘ g ≡ k) → (h ≡ k ∘ f)
    switch-gfʳ {h = h} {k} pf =
      begin
        h
      ↑⟨ cancelRight isoˡ ⟩
        (h ∘ g) ∘ f
      ↓⟨ ∘-resp-≡ˡ pf ⟩
        k ∘ f
      ∎
      where open HomReasoning

  open Switch public