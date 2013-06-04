{-# OPTIONS --universe-polymorphism #-}

module Categories.CategorySolver where

open import Level
open import Categories.Category
open import Categories.Functor hiding (equiv) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_; ∘-resp-≡ to ∘F-resp-≡F)
open import Categories.NaturalTransformation hiding (equiv) renaming (id to idT; _≡_ to _≡T_)


{- We need a way to force the universe levels of two categories to be
   the same, to hack together a reified morphism type.  These lift
   operations let us do this in reification. -}


liftCategory : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
liftCategory {o} {ℓ} {e} {o′} {ℓ′} {e′} C = record {
                                              Obj = Lift {ℓ = o′} (Category.Obj C);
                                              _⇒_ = λ s d → Lift {ℓ = ℓ′} ((lower s) ⇒ (lower d));
                                              _≡_ = λ m₀ m₁ → Lift {ℓ = e′} (lower m₀ ≡ lower m₁);
                                              id = lift id;
                                              _∘_ = λ m₀ m₁ → lift (lower m₀ ∘ lower m₁);
                                              assoc = λ {A} {B} {C₁} {D} {f} {g} {h} → lift C.assoc;
                                              identityˡ = λ {A} {B} {f} → lift C.identityˡ;
                                              identityʳ = λ {A} {B} {f} → lift C.identityʳ;
                                              equiv = record { refl = λ {x} → lift Equiv.refl
                                                             ; sym = λ x → lift (Equiv.sym (lower x))
                                                             ; trans = λ x y → lift (Equiv.trans (lower x) (lower y)) };
                                              ∘-resp-≡ = λ x y → lift (∘-resp-≡ (lower x) (lower y)) }
             where
               module C = Category C
               open C

liftFunctor : ∀ {o₀ ℓ₀ e₀ o′₀ ℓ′₀ e′₀ o₁ ℓ₁ e₁ o′₁ ℓ′₁ e′₁} {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁}
              → Functor C D → Functor (liftCategory {o′ = o′₀} {ℓ′₀} {e′₀} C) (liftCategory {o′ = o′₁} {ℓ′₁} {e′₁} D)
liftFunctor {o₀} {ℓ₀} {e₀} {o′₀} {ℓ′₀} {e′₀} {o₁} {ℓ₁} {e₁} {o′₁} {ℓ′₁} {e′₁} {C} {D} F =
  record {
    F₀ = λ x → lift (F.F₀ (lower x));
    F₁ = λ m → lift (F.F₁ (lower m));
    identity = lift F.identity;
    homomorphism = lift F.homomorphism;
    F-resp-≡ = λ H → lift (F.F-resp-≡ (lower H)) }
  where
    module C = Category C
    module D = Category D
    module ↑C = Category (liftCategory {o′ = o′₀} {ℓ′₀} {e′₀} C)
    module ↑D = Category (liftCategory {o′ = o′₁} {ℓ′₁} {e′₁} D)
    module F = Functor F

mutual
  data ReifiedMorphismHelper {o ℓ e} {C : Category o ℓ e} : Category.Obj C → Category.Obj C → Set (suc (o ⊔ ℓ ⊔ e)) where
    ∥_₁∥₀_ : ∀ {D : Category o ℓ e} → (F : Functor D C) → {s d : Category.Obj D} → (m : ReifiedMorphism {C = D} s d) → ReifiedMorphismHelper (Functor.F₀ F s) (Functor.F₀ F d)

  data ReifiedMorphism {o ℓ e} {C : Category o ℓ e} : Category.Obj C → Category.Obj C → Set (suc (o ⊔ ℓ ⊔ e)) where
    _∥∘∥_ : ∀ {s d d′ : Category.Obj C} → (m2 : ReifiedMorphism {C = C} d d′) → (m1 : ReifiedMorphism {C = C} s d) → ReifiedMorphism s d′
    ∥id∥ : ∀ {x : Category.Obj C} → ReifiedMorphism x x
    ∥_₁∥₁ : ∀ {s d : Category.Obj C} (m : ReifiedMorphismHelper {C = C} s d) → ReifiedMorphism s d
    ∥_∥ : ∀ {s d : Category.Obj C} → (m : Category._⇒_ C s d) → ReifiedMorphism s d

pattern ∥F₁∥m D F s d F₀s F₀d m = ∥_₁∥₁ {F₀s} {F₀d} (∥_₁∥₀_ {D} F {s} {d} m)
pattern ∥_₁∥_ F m = ∥ (∥ F ₁∥₀ m) ₁∥₁

⟱ : ∀ {o ℓ e} → {C : Category o ℓ e} → {s d : Category.Obj C} → ReifiedMorphism {C = C} s d → Category._⇒_ C s d
⟱ {C = C} (∥m₂∥ ∥∘∥ ∥m₁∥) = ⟱ ∥m₂∥ ∘ ⟱ ∥m₁∥
  where open Category C
⟱ {C = C} ∥id∥ = Category.id C
⟱ (∥ F ₁∥ ∥m∥) = Functor.F₁ F (⟱ ∥m∥)
⟱ ∥ m ∥ = m

record ReifiedMorphismOf {o ℓ e} {C : Category o ℓ e} {s d : Category.Obj C} (m : Category._⇒_ C s d) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor reify
  field
    reified : ReifiedMorphism {C = C} s d
    .reified≡ : Category._≡_ C (⟱ {C = C} reified) m

ReifiedMorphismSimplify : ∀ {o ℓ e} → {C : Category o ℓ e} → {s d : Category.Obj C}
                            → (m : ReifiedMorphism {C = C} s d) → ReifiedMorphismOf {C = C} (⟱ m)
ReifiedMorphismSimplify {C = C} ∥ m ∥ = reify ∥ m ∥ (Category.Equiv.refl C)
ReifiedMorphismSimplify {C = C} ∥id∥  = reify ∥id∥ (Category.Equiv.refl C)
ReifiedMorphismSimplify {C = C} (∥m₀∥ ∥∘∥ ∥m₁∥) = ReifiedMorphismSimplify∥∘∥ {∥m₀∥ = ∥m₀∥} {∥m₁∥} (ReifiedMorphismSimplify ∥m₀∥) (ReifiedMorphismSimplify ∥m₁∥)
  where
    module C = Category C
    open C.HomReasoning

    ReifiedMorphismSimplify∥∘∥ : ∀ {s d d′ : C.Obj} → {∥m₀∥ : ReifiedMorphism {C = C} d d′} → {∥m₁∥ : ReifiedMorphism {C = C} s d}
                                 → ReifiedMorphismOf {C = C} (⟱ ∥m₀∥)
                                 → ReifiedMorphismOf {C = C} (⟱ ∥m₁∥)
                                 → ReifiedMorphismOf {C = C} (⟱ (∥m₀∥ ∥∘∥ ∥m₁∥))
    ReifiedMorphismSimplify∥∘∥ {∥m₀∥ = ∥m₀∥} {∥m₁∥} (reify ∥id∥ id≡m₀) (reify ∥m₁∥′ m₁′≡m₁) =
      reify ∥m₁∥′ (begin
                   ⟱ ∥m₁∥′
                 ↑⟨ C.identityˡ ⟩
                   C.id C.∘ ⟱ ∥m₁∥′
                 ↓⟨ C.∘-resp-≡ id≡m₀ m₁′≡m₁ ⟩
                   ⟱ (∥m₀∥ ∥∘∥ ∥m₁∥)
                 ∎)
    ReifiedMorphismSimplify∥∘∥ {∥m₀∥ = ∥m₀∥} {∥m₁∥} (reify ∥m₀∥′ m₀′≡m₀) (reify ∥id∥ id≡m₁) =
      reify ∥m₀∥′ (begin
                   ⟱ ∥m₀∥′
                 ↑⟨ C.identityʳ ⟩
                   ⟱ ∥m₀∥′ C.∘ C.id
                 ↓⟨ C.∘-resp-≡ m₀′≡m₀ id≡m₁ ⟩
                   ⟱ (∥m₀∥ ∥∘∥ ∥m₁∥)
                 ∎)
    ReifiedMorphismSimplify∥∘∥ {∥m₀∥ = ∥m₀∥} {∥m₁∥} (reify (∥m₀₀∥ ∥∘∥ ∥m₀₁∥) m₀₀∘m₀₁≡m₀) (reify ∥m₁∥′ m₁′≡m₁) =
      reify (∥m₀₀∥ ∥∘∥ (∥m₀₁∥ ∥∘∥ ∥m₁∥′)) (begin
                                     ⟱ (∥m₀₀∥ ∥∘∥ (∥m₀₁∥ ∥∘∥ ∥m₁∥′))
                                   ↑⟨ C.assoc ⟩
                                     (⟱ ∥m₀₀∥ C.∘ ⟱ ∥m₀₁∥) C.∘ ⟱ ∥m₁∥′
                                   ↓⟨ C.∘-resp-≡ m₀₀∘m₀₁≡m₀ m₁′≡m₁ ⟩
                                     ⟱ (∥m₀∥ ∥∘∥ ∥m₁∥)
                                   ∎)
    ReifiedMorphismSimplify∥∘∥ (reify ∥m₀∥′ m₀′≡m₀) (reify ∥m₁∥′ m₁′≡m₁) = reify (∥m₀∥′ ∥∘∥ ∥m₁∥′) (C.∘-resp-≡ m₀′≡m₀ m₁′≡m₁)
ReifiedMorphismSimplify {C = C} (∥F₁∥m D F s d ._ ._ ∥m∥) = ReifiedMorphismSimplifyF₀m {s = s} {d} {∥m∥}
                                                              (ReifiedMorphismSimplify ∥m∥)
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    open C.HomReasoning

    ReifiedMorphismSimplifyF₀m : ∀ {s d : D.Obj} → {∥m∥ : ReifiedMorphism {C = D} s d}
                                   → ReifiedMorphismOf {C = D} (⟱ ∥m∥)
                                   → ReifiedMorphismOf {C = C} (F.F₁ (⟱ ∥m∥))
    ReifiedMorphismSimplifyF₀m {∥m∥ = ∥m∥} (reify ∥id∥ id≡m) =
      reify ∥id∥ (begin
                   C.id
                 ↑⟨ F.identity ⟩
                   F.F₁ D.id
                 ↓⟨ F.F-resp-≡ id≡m ⟩
                   F.F₁ (⟱ ∥m∥)
                 ∎)
    ReifiedMorphismSimplifyF₀m {∥m∥ = ∥m∥} (reify (∥m₀∥ ∥∘∥ ∥m₁∥) m₀∘m₁≡m) =
      reify (∥ F ₁∥ ∥m₀∥ ∥∘∥ ∥ F ₁∥ ∥m₁∥) (begin
                                       F.F₁ (⟱ ∥m₀∥) C.∘ F.F₁ (⟱ ∥m₁∥)
                                     ↑⟨ F.homomorphism ⟩
                                       F.F₁ (⟱ ∥m₀∥ D.∘ ⟱ ∥m₁∥)
                                     ↓⟨ F.F-resp-≡ m₀∘m₁≡m ⟩
                                       F.F₁ (⟱ ∥m∥)
                                     ∎)
    ReifiedMorphismSimplifyF₀m {∥m∥ = ∥m∥} (reify ∥m∥′ m′≡m) = reify (∥ F ₁∥ ∥m∥′) (F.F-resp-≡ m′≡m)

.removeIdentities : ∀ {o ℓ e} {C : Category o ℓ e} {s d : Category.Obj C} {m : Category._⇒_ C s d}
                    → (∥m∥ : ReifiedMorphismOf {C = C} m)
                     → Category._≡_ C (⟱ (ReifiedMorphismOf.reified (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m∥)))) m
removeIdentities {C = C} {m = m} ∥m∥ = begin
                                       ⟱
                                         (ReifiedMorphismOf.reified
                                          (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m∥)))
                                      ↓⟨ ReifiedMorphismOf.reified≡ (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m∥)) ⟩
                                        ⟱ (ReifiedMorphismOf.reified ∥m∥)
                                      ↓⟨ ReifiedMorphismOf.reified≡ ∥m∥ ⟩
                                        m
                                      ∎
  where
    module C = Category C
    open C.HomReasoning

.removeIdentities≡ : ∀ {o ℓ e} {C : Category o ℓ e} {s d : Category.Obj C} {m₀ m₁ : Category._⇒_ C s d}
                     → (∥m₀∥ : ReifiedMorphismOf {C = C} m₀)
                     → (∥m₁∥ : ReifiedMorphismOf {C = C} m₁)
                     → Category._≡_ C (⟱ (ReifiedMorphismOf.reified (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₀∥))))
                                      (⟱ (ReifiedMorphismOf.reified (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₁∥))))
                     → Category._≡_ C m₀ m₁
removeIdentities≡ {C = C} {m₀ = m₀} {m₁} ∥m₀∥ ∥m₁∥ m₀≡m₁ =
  begin
    m₀
  ↑⟨ ReifiedMorphismOf.reified≡ ∥m₀∥ ⟩
    ⟱ (ReifiedMorphismOf.reified ∥m₀∥)
  ↑⟨ ReifiedMorphismOf.reified≡
       (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₀∥)) ⟩
    ⟱
      (ReifiedMorphismOf.reified
       (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₀∥)))
  ↓⟨ m₀≡m₁ ⟩
    ⟱
      (ReifiedMorphismOf.reified
       (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₁∥)))
  ↓⟨ ReifiedMorphismOf.reified≡
       (ReifiedMorphismSimplify (ReifiedMorphismOf.reified ∥m₁∥)) ⟩
    ⟱ (ReifiedMorphismOf.reified ∥m₁∥)
  ↓⟨ ReifiedMorphismOf.reified≡ ∥m₁∥ ⟩
    m₁
  ∎
  where
    module C = Category C
    open C.HomReasoning
