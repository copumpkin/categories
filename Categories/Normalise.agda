module Categories.Normalise where

-- Experiments on using computation to simplify equalities

open import Level
open import Function renaming (id to idᶠ; _∘_ to _©_)
open import Data.Product
open import Categories.Support.PropositionalEquality

open import Categories.Category
import Categories.Morphisms as Mor

open import Relation.Binary hiding (_⇒_)

--open import Categories.Object.Coproduct
open import Categories.Object.BinaryCoproducts

open import Categories.Square

-- Normalizing with β and η rules for coproducts, through Yoneda
module +Reasoning {o ℓ e} (C : Category o ℓ e) (bincoprod : BinCoproducts C) where
  
  private module C = Category C
  open C using (Obj; _≡_; _⇒_; module Equiv)
  open Equiv
  open BinCoproducts C bincoprod
--  open BinaryCoproducts C (Bin→Binary C bincoprod) hiding ([_,_]; i₁; i₂; universal; commute₁; commute₂)

  data Ty : Set o where
    ↑_ : Obj -> Ty
    _⊎_ : Ty -> Ty -> Ty

  T : Ty -> Obj
  T (↑ x) = x
  T (t ⊎ t₁) = T t + T t₁

  data Term : Ty → Ty → Set (o ⊔ ℓ) where
    #id : ∀ {A} → Term A A
    #i₁ : ∀ {A B} → Term A (A ⊎ B)
    #i₂ : ∀ {A B} → Term B (A ⊎ B)
    #[_,_] : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C
    _#∘_ : ∀ {A B C} → Term B C → Term A B → Term A C
    `_` : ∀ {A B} → T A ⇒ T B → Term A B

  ↑↑ : ∀ {A B} -> A C.⇒ B -> Term (↑ A) (↑ B)
  ↑↑ {A} {B} f = `_` {↑ A} {↑ B} f

  _#⧻_ : ∀ {A B C D} → (Term A B) → (Term C D) → (Term (A ⊎ C) (B ⊎ D))
  f #⧻ g = #[ #i₁ #∘ f , #i₂ #∘ g ]

  #left : ∀ {A B C} → (Term A B) → (Term (A ⊎ C) (B ⊎ C))
  #left f = f #⧻ #id

  #right : ∀ {A C D} → (Term C D) → (Term (A ⊎ C) (A ⊎ D))
  #right g = #id #⧻ g

  eval : ∀ {A B} → Term A B → T A ⇒ T B
  eval #id = C.id
  eval #i₁ = i₁
  eval #i₂ = i₂
  eval #[ t , t₁ ] = [ (eval t) , (eval t₁) ]
  eval (t #∘ t₁)   = eval t C.∘ eval t₁
  eval ` x `       = x
  
  module Internal where

    _⇛_ : Ty → Ty → Set _
    _⇛_ (↑ x) t = x ⇒ T t
    _⇛_ (s ⊎ s₁) t = (s ⇛ t) × (s₁ ⇛ t)

    ⇛→⇒ : ∀ {A B} → A ⇛ B → T A ⇒ T B
    ⇛→⇒ {↑ O} f = f
    ⇛→⇒ {A ⊎ A₁} (f , g) = [ ⇛→⇒ {A} f , ⇛→⇒ {A₁} g ]

    _<∘_ : ∀ {A B C} → T B ⇒ T C → A ⇛ B → A ⇛ C
    _<∘_ {↑ x} f g = f C.∘ g
    _<∘_ {A ⊎ A₁} f (g₁ , g₂) = (_<∘_ {A} f g₁) , (_<∘_  {A₁} f  g₂)

    .<∘-comm : ∀ {A B C} (f : T B ⇒ T C) (g : A ⇛ B) → f C.∘ (⇛→⇒ {A} g) C.≡ ⇛→⇒ {A} (_<∘_ {A} {B} {C} f g)
    <∘-comm {↑ x} f g = refl
    <∘-comm {A ⊎ A₁} f g = trans ∘[] ([]-cong₂ (<∘-comm f (proj₁ g)) (<∘-comm f (proj₂ g)))

    mutual
     j₁ : ∀ {A B} → A ⇛ (A ⊎ B)
     j₁ {↑ x}    = i₁
     j₁ {A ⊎ A₁} = _<∘_ {A} i₁ (j₁ {A} {A₁}) , _<∘_ {A₁} i₁ (j₂ {A₁} {A})
     j₂ : ∀ {B A} → B ⇛ (A ⊎ B)
     j₂ {↑ x}    = i₂
     j₂ {B ⊎ B₁} = _<∘_ {B} i₂ (j₁ {B} {B₁}) , _<∘_ {B₁} i₂ (j₂ {B₁} {B})
   
     id : ∀ {A} → A ⇛ A
     id {↑ x}    = C.id
     id {A ⊎ A₁} = j₁ {A} {A₁} , j₂ {A₁} {A}

    ⇒→⇛ : ∀ {A B} → T A ⇒ T B → A ⇛ B
    ⇒→⇛ {↑ x} f = f
    ⇒→⇛ {A ⊎ A₁} f = _<∘_ {A} f (j₁ {A} {A₁}) , _<∘_ {A₁} f (j₂ {A₁} {A})

    mutual
     .j₁≡i₁ : ∀ {A B} → ⇛→⇒ {A} (j₁ {A} {B}) C.≡ i₁
     j₁≡i₁ {↑ x} = refl
     j₁≡i₁ {A ⊎ A₁} = universal (trans (C.∘-resp-≡ʳ (sym (j₁≡i₁ {A} {A₁}))) (<∘-comm {A} i₁ (j₁ {A} {A₁}))) 
                                (trans (C.∘-resp-≡ʳ (sym (j₂≡i₂ {A₁} {A}))) (<∘-comm {A₁} i₁ (j₂ {A₁} {A})))
 
     .j₂≡i₂ : ∀ {B A} → ⇛→⇒ {B} (j₂ {B} {A}) C.≡ i₂
     j₂≡i₂ {↑ x} = refl
     j₂≡i₂ {A ⊎ A₁} = universal (trans (C.∘-resp-≡ʳ (sym (j₁≡i₁ {A} {A₁}))) (<∘-comm {A} i₂ (j₁ {A} {A₁}))) 
                                (trans (C.∘-resp-≡ʳ (sym (j₂≡i₂ {A₁} {A})))
                                   (<∘-comm {A₁} i₂ (j₂ {A₁} {A})))

    .iso₁-⇒⇛ : ∀ {A B} → (f : T A ⇒ T B) → ⇛→⇒ {A} {B} (⇒→⇛ {A} {B} f) ≡ f
    iso₁-⇒⇛ {↑ x} f = refl
    iso₁-⇒⇛ {A ⊎ A₁} {B} f = universal (trans (C.∘-resp-≡ʳ (sym j₁≡i₁)) (<∘-comm {A} {A ⊎ A₁} {B} f (j₁ {A}))) 
                                       (trans (C.∘-resp-≡ʳ (sym j₂≡i₂)) (<∘-comm {A₁} {A ⊎ A₁} {B} f (j₂ {A₁})))
     
    .id≡id : ∀ A → ⇛→⇒ {A} (id {A}) ≡ C.id
    id≡id (↑ x) = refl
    id≡id (A ⊎ A₁) = universal (trans C.identityˡ (sym j₁≡i₁)) (trans C.identityˡ (sym j₂≡i₂))

    _∘_ : ∀ {A B C} → B ⇛ C → A ⇛ B → A ⇛ C
    _∘_ {↑ x} {B} f g = ⇛→⇒ {B} f C.∘ g
    _∘_ {A ⊎ A₁} f (g₁ , g₂) = (_∘_ {A} f g₁) , (_∘_ {A₁} f g₂)

    .∘-comm : ∀ {A B C} (f : B ⇛ C) (g : A ⇛ B) → (⇛→⇒ {B} f) C.∘ (⇛→⇒ {A} g) C.≡ ⇛→⇒ {A} (_∘_ {A} {B} {C} f g)
    ∘-comm {↑ x} f g = refl
    ∘-comm {A ⊎ A₁} f g = trans ∘[] ([]-cong₂ (∘-comm f (proj₁ g)) (∘-comm f (proj₂ g)))

    -- An η-expanded version of C
    Cη : Category _ _ _ 
    Cη = record 
      { Obj = Ty
      ; _⇒_ = _⇛_
      ; _≡_ = λ {A} f g → ⇛→⇒ {A} f ≡ ⇛→⇒ {A} g
      ; _∘_ = λ {A} {B} {C} → _∘_ {A} {B} {C}
      ; id = λ {X} → id {X}
      ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → 
                     trans (sym (∘-comm {A} {B} {D} (h ∘ g) f)) 
                    (trans (C.∘-resp-≡ˡ (sym (∘-comm {B} {C} {D} h g))) 
                    (trans C.assoc 
                    (trans (C.∘-resp-≡ʳ (∘-comm {A} {B} {C} g f)) 
                           (∘-comm {A} {C} {D} h (g ∘ f)))))
      ; identityˡ = λ {A} {B} {f} → trans (sym (∘-comm {A} {B} {B} id f)) 
                                   (trans (C.∘-resp-≡ˡ (id≡id B)) C.identityˡ)
      ; identityʳ = λ {A} {B} {f} →
                      trans (sym (∘-comm {A} {A} {B} f id))
                     (trans (C.∘-resp-≡ʳ (id≡id A)) C.identityʳ)
      ; equiv = record 
        { refl = refl
        ; sym = sym
        ; trans = trans
        }
      ; ∘-resp-≡ = λ {A} {B} {C} {f} {h} {g} {i} f≡h g≡i → 
            trans (sym (∘-comm {A} {B} {C} f g)) (trans (C.∘-resp-≡ f≡h g≡i) (∘-comm {A} {B} {C} h i))
      }
 


    module Cη = Category Cη

    -- We need the opposite category for Yon because i₁ and i₂ simplify when precomposed.
    -- Using Eda seems to undo the simplifications instead.
    open Yon-Eda (Category.op Cη)
 
    Yon-i₁ : ∀ {A B} → Yon (A ⊎ B) A
    Yon-i₁ {A} {B} = record
                     { arr = j₁ {A} {B}
                     ; fun = proj₁
                     ; ok = λ {W} f → trans (trans (sym commute₁) (C.∘-resp-≡ʳ (sym (j₁≡i₁ {A} {B})))) (∘-comm {A} {A ⊎ B} {W} f (j₁ {A} {B}))
                     }

    Yon-i₂ : ∀ {A B} → Yon (A ⊎ B) B
    Yon-i₂ {A} {B} = record
                     { arr = j₂ {B} {A}
                     ; fun = proj₂
                     ; ok = λ {W} f →
                                trans (trans (sym commute₂) (C.∘-resp-≡ʳ (sym (j₂≡i₂ {B} {A}))))
                                (∘-comm {B} {A ⊎ B} {W} f (j₂ {B} {A}))
                     }

    Yon-[_,_] : ∀ {A B C} → Yon C A → Yon C B → Yon C (A ⊎ B)
    Yon-[_,_] f g = record
                    { arr = (Yon.arr f) , (Yon.arr g)
                    ; fun = λ f₁ → (Yon.fun f f₁) , (Yon.fun g f₁)
                    ; ok = λ f₁ → []-cong₂ (Yon.ok f f₁) (Yon.ok g f₁)
                    }

  
    eeval : ∀ {A B} → Term A B → Yon B A
    eeval #id = Yon-id
    eeval #i₁ = Yon-i₁
    eeval #i₂ = Yon-i₂
    eeval #[ t , t₁ ] = Yon-[ (eeval t) , (eeval t₁) ]
    eeval (t #∘ t₁) = Yon-compose (eeval t₁) (eeval t)
    eeval {A} ` f ` = Yon-inject (⇒→⇛ {A} f)

    yeeval : ∀ {A B} → Term A B → T A ⇒ T B
    yeeval {A} {B} t = ⇛→⇒ {A} (Yon.arr (eeval t))

    .yeeval≡eval : ∀ {A B} → (f : Term A B) → yeeval f ≡ eval f
    yeeval≡eval     #id = id≡id _
    yeeval≡eval {A} #i₁ = j₁≡i₁ {A}
    yeeval≡eval {A} #i₂ = j₂≡i₂ {A}
    yeeval≡eval   ` x ` = iso₁-⇒⇛ x
    yeeval≡eval #[ f , f₁ ] = []-cong₂ (yeeval≡eval f) (yeeval≡eval f₁)
    yeeval≡eval (f #∘ f₁) = trans
                          (trans (Yon.ok (eeval f₁) (Yon.arr (eeval f)))
                                 (sym (∘-comm (Yon.arr (eeval f)) (Yon.arr (eeval f₁)))))
                          (C.∘-resp-≡ (yeeval≡eval f) (yeeval≡eval f₁))

    +reasoning : NormReasoning C o (ℓ ⊔ o)
    +reasoning = record
                 { U = Ty 
                 ; T = T 
                 ; _#⇒_ = Term 
                 ; eval = eval 
                 ; norm = yeeval 
                 ; norm≡eval = yeeval≡eval }
  
  open NormReasoning Internal.+reasoning public hiding (T; eval)
