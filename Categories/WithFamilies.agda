module Categories.WithFamilies where

open import Level
import Relation.Binary.HeterogeneousEquality as Het
open Het using (_≅_)

open import Categories.Support.PropositionalEquality
open import Categories.Support.Experimental

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalIsomorphism
open import Categories.Object.Terminal

open import Categories.Fam

module UnpackFam {o ℓ e a b} (C : Category o ℓ e)
                 (T : Functor (Category.op C) (Fam a b)) where
  private module C = Category C
  private module T = Functor T

  Context = C.Obj
  
  Ty : C.Obj → Set a
  Ty Γ = Fam.U (T.F₀ Γ)

  _[_] : ∀ {Γ Δ} → Ty Γ → Δ C.⇒ Γ → Ty Δ
  _[_] A f = Fam.Hom.f (T.F₁ f) A

  Tm : ∀ Γ → Ty Γ → Set b  
  Tm Γ = Fam.T (T.F₀ Γ)

  _[_⁺] : ∀ {Γ Δ A} → Tm Γ A → (f : Δ C.⇒ Γ) → Tm Δ (A [ f ])
  _[_⁺] M f = Fam.Hom.φ (T.F₁ f) _ M

record CwF {o ℓ e a b} : Set (suc e ⊔ (suc ℓ ⊔ suc o) ⊔ suc a ⊔ suc b) where
  field
    C : Category o ℓ e
    T : Functor (Category.op C) (Fam a b)
    Empty : Terminal C
  
  module C = Category C
  module T = Functor T
  open UnpackFam C T
  module Empty = Terminal C Empty

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

  v[_] : ∀ {Γ A Δ} → (γ : Δ C.⇒ Γ) -> Tm (Δ > A [ γ ]) (A [ γ C.∘ p ])
  v[_] {Γ} {A} {Δ} γ = ≣-subst′ (Tm (Δ > A [ γ ])) (≣-sym (Fam.Eq.f≡g (T.homomorphism {Γ}) {A})) (v {Δ} {A [ γ ]})

  _[id] : ∀ {Γ A} -> Tm Γ A -> Tm Γ (A [ C.id ])
  _[id] {Γ} {A} x = ≣-subst′ (Tm Γ) (≣-sym (Fam.Eq.f≡g (T.identity {Γ}) {A})) x

  open UnpackFam C T public
  open Empty public using () renaming (⊤ to <>)
  


record Pi {o ℓ e a b} (Cwf : CwF {o} {ℓ} {e} {a} {b}) : Set (o ⊔ ℓ ⊔ a ⊔ b) where
  open CwF Cwf
  field
    Π : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ > A)) -> Ty Γ
    lam : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) -> Tm Γ (Π A B)
    _$_ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> 
            (f : Tm Γ (Π A B)) (x : Tm Γ A) -> Tm Γ (B [ < C.id , x [id] > ])

    -- naturality laws
    .Π-nat   : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ > A)) -> ∀ {Δ} (γ : Δ C.⇒ Γ) 
                     -> Π A B [ γ ] ≣ Π (A [ γ ]) (B [ < (γ C.∘ p) , v[ γ ] > ])
    .lam-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) -> ∀ {Δ} (γ : Δ C.⇒ Γ) 
                     -> lam b [ γ ⁺] ≅ lam {A = A [ γ ]} (b [ < γ C.∘ p , v[ γ ] > ⁺])
    .app-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (f : Tm Γ (Π A B)) (x : Tm Γ A) -> ∀ {Δ} (γ : Δ C.⇒ Γ) 
                     -> (f $ x) [ γ ⁺] ≅ ≣-subst′ (Tm Δ) (Π-nat A B γ) (f [ γ ⁺]) $ (x [ γ ⁺])

    -- proofs of the lam/_$_ isomorphism
    .β : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) (x : Tm Γ A) 
           -> (lam b $ x) ≣ b [ < C.id , x [id] > ⁺]

    .η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (f : Tm Γ (Π A B)) 
           -> lam (≣-subst′ (Tm (Γ > A)) (Π-nat A B p) (f [ p ⁺]) $ v) ≅ f

    
