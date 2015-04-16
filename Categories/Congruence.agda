module Categories.Congruence where

open import Level
open import Relation.Binary hiding (_⇒_; Setoid)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning

open import Categories.Category hiding (module Heterogeneous; _[_∼_])

record Congruence {o ℓ e} (C : Category o ℓ e) q : Set (o ⊔ ℓ ⊔ e ⊔ suc q) where
  open Category C
  field
    _≡₀_ : Rel Obj q
    equiv₀ : IsEquivalence _≡₀_

  module Equiv₀ = IsEquivalence equiv₀

  field
    coerce : ∀ {X₁ X₂ Y₁ Y₂} → X₁ ≡₀ X₂ → Y₁ ≡₀ Y₂ → X₁ ⇒ Y₁ → X₂ ⇒ Y₂

    .coerce-resp-≡ : ∀ {X₁ X₂ Y₁ Y₂} (xpf : X₁ ≡₀ X₂) (ypf : Y₁ ≡₀ Y₂)
                   → {f₁ f₂ : X₁ ⇒ Y₁} → f₁ ≡ f₂
                   → coerce xpf ypf f₁ ≡ coerce xpf ypf f₂
    .coerce-refl : ∀ {X Y} (f : X ⇒ Y) → coerce Equiv₀.refl Equiv₀.refl f ≡ f
    .coerce-invariant : ∀ {X₁ X₂ Y₁ Y₂} (xpf₁ xpf₂ : X₁ ≡₀ X₂)
                                        (ypf₁ ypf₂ : Y₁ ≡₀ Y₂)
                      → (f : X₁ ⇒ Y₁)
                      → coerce xpf₁ ypf₁ f ≡ coerce xpf₂ ypf₂ f
    .coerce-trans : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} (xpf₁ : X₁ ≡₀ X₂) (xpf₂ : X₂ ≡₀ X₃)
                                          (ypf₁ : Y₁ ≡₀ Y₂) (ypf₂ : Y₂ ≡₀ Y₃)
                  → (f : X₁ ⇒ Y₁)
                  →   coerce (Equiv₀.trans xpf₁ xpf₂) (Equiv₀.trans ypf₁ ypf₂) f
                    ≡ coerce xpf₂ ypf₂ (coerce xpf₁ ypf₁ f)
    .coerce-∘ : ∀ {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
              →   (pfX : X₁ ≡₀ X₂) (pfY : Y₁ ≡₀ Y₂) (pfZ : Z₁ ≡₀ Z₂)
              →   (g : Y₁ ⇒ Z₁) (f : X₁ ⇒ Y₁)
              → coerce pfX pfZ (g ∘ f) ≡ coerce pfY pfZ g ∘ coerce pfX pfY f


  .coerce-local : ∀ {X Y} (xpf : X ≡₀ X) (ypf : Y ≡₀ Y) {f : X ⇒ Y} → coerce xpf ypf f ≡ f
  coerce-local xpf ypf {f} =
    begin
      coerce xpf ypf f
    ↓⟨ coerce-invariant xpf Equiv₀.refl ypf Equiv₀.refl f ⟩
      coerce Equiv₀.refl Equiv₀.refl f
    ↓⟨ coerce-refl f ⟩
      f
    ∎
    where open HomReasoning

  .coerce-zigzag : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ≡₀ X₂) (rfX : X₂ ≡₀ X₁)
                                   (pfY : Y₁ ≡₀ Y₂) (rfY : Y₂ ≡₀ Y₁)
                   → {f : X₁ ⇒ Y₁}
                   → coerce rfX rfY (coerce pfX pfY f) ≡ f
  coerce-zigzag pfX rfX pfY rfY {f} =
    begin
      coerce rfX rfY (coerce pfX pfY f)
    ↑⟨ coerce-trans _ _ _ _ _ ⟩
      coerce (trans pfX rfX) (trans pfY rfY) f
    ↓⟨ coerce-local _ _ ⟩
      f
    ∎
    where
    open HomReasoning
    open Equiv₀

  .coerce-uncong : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ≡₀ X₂) (pfY : Y₁ ≡₀ Y₂) (f g : X₁ ⇒ Y₁) → coerce pfX pfY f ≡ coerce pfX pfY g → f ≡ g
  coerce-uncong xpf ypf f g fg-pf =
    begin
      f
    ↑⟨ coerce-zigzag _ _ _ _ ⟩
      coerce (sym xpf) (sym ypf) (coerce xpf ypf f)
    ↓⟨ coerce-resp-≡ _ _ fg-pf ⟩
      coerce (sym xpf) (sym ypf) (coerce xpf ypf g)
    ↓⟨ coerce-zigzag _ _ _ _ ⟩
      g
    ∎
    where
    open HomReasoning
    open Equiv₀

  .coerce-slide⇒ : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ≡₀ X₂) (rfX : X₂ ≡₀ X₁)
                                   (pfY : Y₁ ≡₀ Y₂) (rfY : Y₂ ≡₀ Y₁)
                   → (f : X₁ ⇒ Y₁) (g : X₂ ⇒ Y₂)
                   → coerce pfX pfY f ≡ g → f ≡ coerce rfX rfY g
  coerce-slide⇒ pfX rfX pfY rfY f g eq =
    begin
      f
    ↑⟨ coerce-zigzag _ _ _ _ ⟩
      coerce rfX rfY (coerce pfX pfY f)
    ↓⟨ coerce-resp-≡ _ _ eq ⟩
      coerce rfX rfY g
    ∎
    where open HomReasoning

  .coerce-slide⇐ : ∀ {X₁ X₂ Y₁ Y₂} (pfX : X₁ ≡₀ X₂) (rfX : X₂ ≡₀ X₁)
                                   (pfY : Y₁ ≡₀ Y₂) (rfY : Y₂ ≡₀ Y₁)
                   → (f : X₁ ⇒ Y₁) (g : X₂ ⇒ Y₂)
                   → f ≡ coerce rfX rfY g → coerce pfX pfY f ≡ g
  coerce-slide⇐ pfX rfX pfY rfY f g eq =
    begin
      coerce pfX pfY f
    ↓⟨ coerce-resp-≡ _ _ eq ⟩
      coerce pfX pfY (coerce rfX rfY g)
    ↓⟨ coerce-zigzag _ _ _ _ ⟩
      g
    ∎
    where open HomReasoning

  .coerce-id : ∀ {X Y} (pf₁ pf₂ : X ≡₀ Y) → coerce pf₁ pf₂ id ≡ id
  coerce-id pf₁ pf₂ = 
    begin
      coerce pf₁ pf₂ id
    ↑⟨ identityˡ ⟩
      id ∘ coerce pf₁ pf₂ id
    ↑⟨ ∘-resp-≡ˡ (coerce-local _ _) ⟩
      coerce (trans (sym pf₂) pf₂) (trans (sym pf₂) pf₂) id ∘ coerce pf₁ pf₂ id
    ↓⟨ ∘-resp-≡ˡ (coerce-trans _ _ _ _ _) ⟩
      coerce pf₂ pf₂ (coerce (sym pf₂) (sym pf₂) id) ∘ coerce pf₁ pf₂ id
    ↑⟨ coerce-∘ _ _ _ _ _ ⟩
      coerce pf₁ pf₂ (coerce (sym pf₂) (sym pf₂) id ∘ id)
    ↓⟨ coerce-resp-≡ _ _ identityʳ ⟩
      coerce pf₁ pf₂ (coerce (sym pf₂) (sym pf₂) id)
    ↑⟨ coerce-trans _ _ _ _ _ ⟩
      coerce (trans (sym pf₂) pf₁) (trans (sym pf₂) pf₂) id
    ↓⟨ coerce-local _ _ ⟩
      id
    ∎
    where
    open HomReasoning
    open Equiv₀

module Heterogeneous {o ℓ e} {C : Category o ℓ e} {q} (Q : Congruence C q) where
  open Category C
  open Congruence Q
  open Equiv renaming (refl to refl′; sym to sym′; trans to trans′; reflexive to reflexive′)
  open Equiv₀ renaming (refl to refl₀; sym to sym₀; trans to trans₀; reflexive to reflexive₀)

  infix 4 _∼_

  data _∼_ {A B} (f : A ⇒ B) {X Y} (g : X ⇒ Y) : Set (o ⊔ ℓ ⊔ e ⊔ q) where
    ≡⇒∼ : (ax : A ≡₀ X) (by : B ≡₀ Y) → .(coerce ax by f ≡ g) → f ∼ g

  refl : ∀ {A B} {f : A ⇒ B} → f ∼ f
  refl = ≡⇒∼ refl₀ refl₀ (coerce-refl _)

  sym : ∀ {A B} {f : A ⇒ B} {D E} {g : D ⇒ E} → f ∼ g → g ∼ f
  sym (≡⇒∼ A≡D B≡E f≡g) = ≡⇒∼ (sym₀ A≡D) (sym₀ B≡E) (coerce-slide⇐ _ _ _ _ _ _ (sym′ f≡g))

  trans : ∀ {A B} {f : A ⇒ B} 
             {D E} {g : D ⇒ E}
             {F G} {h : F ⇒ G}
          → f ∼ g → g ∼ h → f ∼ h
  trans (≡⇒∼ A≡D B≡E f≡g) (≡⇒∼ D≡F E≡G g≡h) = ≡⇒∼
    (trans₀ A≡D D≡F)
    (trans₀ B≡E E≡G)
    (trans′ (trans′ (coerce-trans _ _ _ _ _) (coerce-resp-≡ _ _ f≡g)) g≡h)

  reflexive : ∀ {A B} {f g : A ⇒ B} → f ≣ g → f ∼ g
  reflexive f≣g = ≡⇒∼ refl₀ refl₀ (trans′ (coerce-refl _) (reflexive′ f≣g))

  ∘-resp-∼ : ∀ {A B C A′ B′ C′} {f : B ⇒ C} {h : B′ ⇒ C′} {g : A ⇒ B} {i : A′ ⇒ B′} → f ∼ h → g ∼ i → (f ∘ g) ∼ (h ∘ i)
  ∘-resp-∼ {f = f} {h} {g} {i} (≡⇒∼ B≡B′₁ C≡C′ f≡h) (≡⇒∼ A≡A′ B≡B′₂ g≡i) = ≡⇒∼
    A≡A′
    C≡C′
    (begin
      coerce A≡A′ C≡C′ (f ∘ g)
    ↓⟨ coerce-∘ _ _ _ _ _ ⟩
      coerce B≡B′₁ C≡C′ f ∘ coerce A≡A′ B≡B′₁ g
    ↓⟨ ∘-resp-≡ʳ (coerce-invariant _ _ _ _ _) ⟩
      coerce B≡B′₁ C≡C′ f ∘ coerce A≡A′ B≡B′₂ g
    ↓⟨ ∘-resp-≡ f≡h g≡i ⟩
      h ∘ i
    ∎)
    where open HomReasoning

  ∘-resp-∼ˡ : ∀ {A B C C′} {f : B ⇒ C} {h : B ⇒ C′} {g : A ⇒ B} → f ∼ h → (f ∘ g) ∼ (h ∘ g)
  ∘-resp-∼ˡ {f = f} {h} {g} (≡⇒∼ B≡B C≡C′ f≡h) = ≡⇒∼ refl₀ C≡C′
    (begin
      coerce refl₀ C≡C′ (f ∘ g)
    ↓⟨ coerce-∘ _ _ _ _ _ ⟩
      coerce B≡B C≡C′ f ∘ coerce refl₀ B≡B g
    ↓⟨ ∘-resp-≡ʳ (coerce-local _ _) ⟩
      coerce B≡B C≡C′ f ∘ g
    ↓⟨ ∘-resp-≡ˡ f≡h ⟩
      h ∘ g
    ∎)
    where open HomReasoning

  ∘-resp-∼ʳ : ∀ {A A′ B C} {f : A ⇒ B} {h : A′ ⇒ B} {g : B ⇒ C} → f ∼ h → (g ∘ f) ∼ (g ∘ h)
  ∘-resp-∼ʳ {f = f} {h} {g} (≡⇒∼ A≡A′ B≡B f≡h) = ≡⇒∼ A≡A′ refl₀
    (begin
      coerce A≡A′ refl₀ (g ∘ f)
    ↓⟨ coerce-∘ _ _ _ _ _ ⟩
      coerce B≡B refl₀ g ∘ coerce A≡A′ B≡B f
    ↓⟨ ∘-resp-≡ˡ (coerce-local _ _) ⟩
      g ∘ coerce A≡A′ B≡B f
    ↓⟨ ∘-resp-≡ʳ f≡h ⟩
      g ∘ h
    ∎)
    where open HomReasoning

  .∼⇒≡ : ∀ {A B} {f g : A ⇒ B} → f ∼ g → f ≡ g
  ∼⇒≡ (≡⇒∼ A≡A B≡B f≡g) = trans′ (sym′ (coerce-local A≡A B≡B)) (irr f≡g)

  domain-≣ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → A ≡₀ A′
  domain-≣ (≡⇒∼ eq _ _) = eq

  codomain-≣ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → B ≡₀ B′
  codomain-≣ (≡⇒∼ _ eq _) = eq

  ∼-cong : ∀ {t : Level} {T : Set t} {dom cod : T → Obj} (f : (x : T) → dom x ⇒ cod x) → ∀ {i j} (eq : i ≣ j) → f i ∼ f j
  ∼-cong f ≣-refl = refl

  -- henry ford versions
  .∼⇒≡₂ : ∀ {A A′ B B′} {f : A ⇒ B} {f′ : A′ ⇒ B′} → f ∼ f′ → (A≡A′ : A ≡₀ A′) (B≡B′ : B ≡₀ B′) → coerce A≡A′ B≡B′ f ≡ f′
  ∼⇒≡₂ (≡⇒∼ pfA pfB pff) A≡A′ B≡B′ = trans′ (coerce-invariant _ _ _ _ _) (irr pff)

  -- .∼⇒≡ˡ : ∀ {A B B′} {f : A ⇒ B} {f′ : A ⇒ B′} → f ∼ f′ → (B≣B′ : B ≣ B′) → floatˡ B≣B′ f ≡ f′
  -- ∼⇒≡ˡ pf ≣-refl = ∼⇒≡ pf

  -- .∼⇒≡ʳ : ∀ {A A′ B} {f : A ⇒ B} {f′ : A′ ⇒ B} → f ∼ f′ → (A≣A′ : A ≣ A′) → floatʳ A≣A′ f ≡ f′
  -- ∼⇒≡ʳ pf ≣-refl = ∼⇒≡ pf

  -- ≡⇒∼ʳ : ∀ {A A′ B} {f : A ⇒ B} {f′ : A′ ⇒ B} → (A≣A′ : A ≣ A′) → .(floatʳ A≣A′ f ≡ f′) → f ∼ f′
  -- ≡⇒∼ʳ ≣-refl pf = ≡⇒∼ pf

  coerce-resp-∼ : ∀ {A A′ B B′} (A≡A′ : A ≡₀ A′) (B≡B′ : B ≡₀ B′) {f : C [ A , B ]} → f ∼ coerce A≡A′ B≡B′ f
  coerce-resp-∼ A≡A′ B≡B′ = ≡⇒∼ A≡A′ B≡B′ refl′

  -- floatˡ-resp-∼ : ∀ {A B B′} (B≣B′ : B ≣ B′) {f : C [ A , B ]} → f ∼ floatˡ B≣B′ f
  -- floatˡ-resp-∼ ≣-refl = refl

  -- floatʳ-resp-∼ : ∀ {A A′ B} (A≣A′ : A ≣ A′) {f : C [ A , B ]} → f ∼ floatʳ A≣A′ f
  -- floatʳ-resp-∼ ≣-refl = refl

  infixr 4 ▹_

  record -⇒- : Set (o ⊔ ℓ) where
    constructor ▹_
    field
      {Dom} : Obj
      {Cod} : Obj
      morphism : Dom ⇒ Cod

  ∼-setoid : Setoid _ _
  ∼-setoid = record {
               Carrier = -⇒-;
               _≈_ = λ x y → -⇒-.morphism x ∼ -⇒-.morphism y;
               isEquivalence = record { refl = refl; sym = sym; trans = trans } }

  module HetReasoning where
    open SetoidReasoning ∼-setoid public

_[_∼_] : ∀ {o ℓ e} {C : Category o ℓ e} {q} (Q : Congruence C q) {A B} (f : C [ A , B ]) {X Y} (g : C [ X , Y ]) → Set (q ⊔ o ⊔ ℓ ⊔ e)
Q [ f ∼ g ] = Heterogeneous._∼_ Q f g

TrivialCongruence : ∀ {o ℓ e} (C : Category o ℓ e) → Congruence C _
TrivialCongruence C = record
  { _≡₀_ = _≣_
  ; equiv₀ = ≣-isEquivalence
  ; coerce = ≣-subst₂ (_⇒_)
  ; coerce-resp-≡ = resp-≡
  ; coerce-refl = λ f → refl
  ; coerce-invariant = invariant
  ; coerce-trans = tranz
  ; coerce-∘ = compose
  }
  where
  open Category C
  open Equiv
  -- XXX must this depend on proof irrelevance?

  .resp-≡ : ∀ {X₁ X₂ Y₁ Y₂} (xpf : X₁ ≣ X₂) (ypf : Y₁ ≣ Y₂) {f₁ f₂ : X₁ ⇒ Y₁}
            → f₁ ≡ f₂ → ≣-subst₂ _⇒_ xpf ypf f₁ ≡ ≣-subst₂ _⇒_ xpf ypf f₂
  resp-≡ ≣-refl ≣-refl eq = eq

  .invariant : ∀ {X₁ X₂ Y₁ Y₂} (xpf₁ xpf₂ : X₁ ≣ X₂) (ypf₁ ypf₂ : Y₁ ≣ Y₂)
               → (f : X₁ ⇒ Y₁)
               → ≣-subst₂ _⇒_ xpf₁ ypf₁ f ≡ ≣-subst₂ _⇒_ xpf₂ ypf₂ f
  invariant ≣-refl ≣-refl ≣-refl ≣-refl f = refl

  .tranz : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} (xpf₁ : X₁ ≣ X₂) (xpf₂ : X₂ ≣ X₃)
                                 (ypf₁ : Y₁ ≣ Y₂) (ypf₂ : Y₂ ≣ Y₃)
           → (f : X₁ ⇒ Y₁)
           →   ≣-subst₂ _⇒_ (≣-trans xpf₁ xpf₂) (≣-trans ypf₁ ypf₂) f
             ≡ ≣-subst₂ _⇒_ xpf₂ ypf₂ (≣-subst₂ _⇒_ xpf₁ ypf₁ f)
  tranz ≣-refl xpf₂ ≣-refl ypf₂ f = refl

  .compose : ∀ {X₁ X₂ Y₁ Y₂ Z₁ Z₂} (pfX : X₁ ≣ X₂)(pfY : Y₁ ≣ Y₂)(pfZ : Z₁ ≣ Z₂)
             → (g : Y₁ ⇒ Z₁) (f : X₁ ⇒ Y₁)
             →   ≣-subst₂ _⇒_ pfX pfZ (g ∘ f)
               ≡ ≣-subst₂ _⇒_ pfY pfZ g ∘ ≣-subst₂ _⇒_ pfX pfY f
  compose ≣-refl ≣-refl ≣-refl g f = refl
