module Categories.WithFamilies where

open import Level
import Relation.Binary.HeterogeneousEquality as Het
open Het using (_≅_)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalIsomorphism
open import Categories.Object.Terminal

open import Categories.Fam


record CwF {o ℓ e a b} : Set (suc e ⊔ (suc ℓ ⊔ suc o) ⊔ suc a ⊔ suc b) where
  field
    C : Category o ℓ e
    T : Functor (Category.op C) (Fam a b)
    Empty : Terminal C
  
  module C = Category C
  module T = Functor T
  module Empty = Terminal C Empty
  open Empty using () renaming (⊤ to <>)
  
  Ty : C.Obj → Set a
  Ty Γ = Fam.U (T.F₀ Γ)

  _[_] : ∀ {Γ Δ} → Ty Γ → Δ C.⇒ Γ → Ty Δ
  _[_] A f = Fam.Hom.f (T.F₁ f) A

  Tm : ∀ Γ → Ty Γ → Set b  
  Tm Γ = Fam.T (T.F₀ Γ)

  _[_⁺] : ∀ {Γ Δ A} → Tm Γ A → (f : Δ C.⇒ Γ) → Tm Δ (A [ f ])
  _[_⁺] M f = Fam.Hom.φ (T.F₁ f) _ M

  field
    -- context snoc
    _>_ : ∀ Γ → Ty Γ → C.Obj
    -- projections
    p : ∀ {Γ A} → (Γ > A) C.⇒ Γ
    v : ∀ {Γ A} → Tm (Γ > A) (A [ p ])
    -- constructor
    <_,_>         : ∀ {Γ A} → ∀ {Δ} (γ : Δ C.⇒ Γ) (a : Tm Δ (A [ γ ])) → Δ C.⇒ (Γ > A)
    .p∘<γ,a>≡γ    : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} → p C.∘ < γ , a > C.≡ γ
    .v[<γ,a>]≡a   : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} → v [ < γ , a > ⁺] ≅ a
    .<γ,a>-unique : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} → 
                      (δ : Δ C.⇒ (Γ > A)) → .(p C.∘ δ C.≡ γ) → .(v [ δ ⁺] ≅ a) → δ C.≡ < γ , a >
