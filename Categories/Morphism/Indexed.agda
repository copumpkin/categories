{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category
open import Categories.Support.Equivalence

module Categories.Morphism.Indexed {o ℓ e c q} (C : Category o ℓ e) (B : Setoid c q) where

open import Level using (_⊔_)
open import Data.Product as P using (_,_; _×_)
open import Function as F using () renaming (_∘_ to _⋆_; _∘′_ to _⋆′_)
open import Relation.Binary as B using ()
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import Categories.Support.PropositionalEquality
open import Categories.Support.SetoidFunctions as SF using (_⟶_; ⟪_,_⟫′)
open import Categories.Support.SetoidPi as SΠ public using (Π; IndexedSetoid) renaming (_⟨$⟩_ to _‼_; cong to cong₁)

import Categories.Object.Indexed as IxOb
open IxOb C B
open Category C
open Heterogeneous C

open Setoid B using () renaming (Carrier to Bc; _≈_ to _≈B_)

open Setoid using () renaming (_≈_ to _[_≈_])

ihom-setoid : {S : Set o} → (S → (Obj × Obj)) → (B ⟶ (set→setoid S)) → IndexedSetoid Bc _≈B_ _ _
ihom-setoid {S} F Xs = record
      -- ok, this is massively ugly, but it gets around some weird problems introduced in 2.5.1.1 (JC)
  { Carrier = λ i → (P.proj₁ (F (_⟶_._⟨$⟩_ Xs i)) ⇒ P.proj₂ (F (_⟶_._⟨$⟩_ Xs i)))
  ; _≈_ = λ f g → f ∼ g
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; resp = λ {i} {j} i≈j → SΠ.resp-per′ (at′ i) (at′ j) (resp₁ i≈j) (resp₂ i≈j)
  }
  where
  
  -- fake 'at' for resp
  at′ : Bc → Setoid _ _
  at′ i = record
    { Carrier = (P.proj₁ (F (_⟶_._⟨$⟩_ Xs i)) ⇒ P.proj₂ (F (_⟶_._⟨$⟩_ Xs i)))
    ; _≈_ = λ f g → f ∼ g
    ; isEquivalence = record { refl = refl; sym = sym; trans = trans }
    }

  at-≈ : (X : S) → B.Rel ((P.uncurry _⇒_ ⋆′ F) X) (ℓ ⊔ e)
  at-≈ X = λ f g → f ∼ g

  .resp₁ : ∀ {i j} → (i ≈B j) → (P.proj₁ (F (_⟶_._⟨$⟩_ Xs i)) ⇒ P.proj₂ (F (_⟶_._⟨$⟩_ Xs i))) ≣ (P.proj₁ (F (_⟶_._⟨$⟩_ Xs j)) ⇒ P.proj₂ (F (_⟶_._⟨$⟩_ Xs j)))
  resp₁ i≈j = ≣-cong (P.uncurry _⇒_ ⋆′ F) (cong₀ Xs i≈j)

  .resp₂ : ∀ {i j} → (i ≈B j) → Setoid._≈_ (at′ i) ≅ Setoid._≈_ (at′ j)
  resp₂ i≈j = HE.cong at-≈ (HE.≡-to-≅ (cong₀ Xs i≈j))

Fan : Obj → Dust → Set _
Fan X Ys = Π B (ihom-setoid (λ Y → X , Y) Ys)

fan-setoid : Obj → Dust → Setoid _ _
fan-setoid X Ys = SΠ.setoid B (ihom-setoid (λ Y → X , Y) Ys)

_⇒∗_ = Fan
_⇨∗_ = fan-setoid

Plume : Dust → Obj → Set _
Plume Xs Y = Π B (ihom-setoid (λ X → X , Y) Xs)

plume-setoid : Dust → Obj → Setoid _ _
plume-setoid Xs Y = SΠ.setoid B (ihom-setoid (λ X → X , Y) Xs)

_∗⇒_ = Plume
_∗⇨_ = plume-setoid

Dance : Dust → Dust → Set _
Dance Xs Ys = Π B (ihom-setoid F.id ⟪ Xs , Ys ⟫′)

dance-setoid : Dust → Dust → Setoid _ _
dance-setoid Xs Ys = SΠ.setoid B (ihom-setoid F.id ⟪ Xs , Ys ⟫′)

_∗⇒∗_ = Dance
_∗⇨∗_ = dance-setoid

_◃_ : ∀ {Xs Y Z} (f : Y ⇒ Z) (g : Xs ∗⇒ Y) → Xs ∗⇒ Z
f ◃ g = record { _⟨$⟩_ = λ x → f ∘ (g ‼ x)
               ; cong = λ x≈y → ∘-resp-∼ʳ (cong₁ g x≈y) }

_▹_ : ∀ {X Y Zs} (f : Y ⇒∗ Zs) (g : X ⇒ Y) → X ⇒∗ Zs
f ▹ g = record { _⟨$⟩_ = λ x → (f ‼ x) ∘ g
               ; cong = λ x≈y → ∘-resp-∼ˡ (cong₁ f x≈y) }

_⋊_ : ∀ {Xs Ys Z} (f : Ys ∗⇒ Z) (g : Xs ∗⇒∗ Ys) → Xs ∗⇒ Z
f ⋊ g = record { _⟨$⟩_ = λ x → (f ‼ x) ∘ (g ‼ x)
               ; cong = λ x≈y → ∘-resp-∼ (cong₁ f x≈y) (cong₁ g x≈y) }

_⋉_ : ∀ {X Ys Zs} (f : Ys ∗⇒∗ Zs) (g : X ⇒∗ Ys) → X ⇒∗ Zs
f ⋉ g = record { _⟨$⟩_ = λ x → (f ‼ x) ∘ (g ‼ x)
               ; cong = λ x≈y → ∘-resp-∼ (cong₁ f x≈y) (cong₁ g x≈y) }

_⋈_ : ∀ {Xs Y Zs} (f : Y ⇒∗ Zs) (g : Xs ∗⇒ Y) → Xs ∗⇒∗ Zs
f ⋈ g = record { _⟨$⟩_ = λ x → (f ‼ x) ∘ (g ‼ x)
               ; cong = λ x≈y → ∘-resp-∼ (cong₁ f x≈y) (cong₁ g x≈y) }

_◽_ : ∀ {Xs Ys Zs} (f : Ys ∗⇒∗ Zs) (g : Xs ∗⇒∗ Ys) → Xs ∗⇒∗ Zs
f ◽ g = record { _⟨$⟩_ = λ x → (f ‼ x) ∘ (g ‼ x)
               ; cong = λ x≈y → ∘-resp-∼ (cong₁ f x≈y) (cong₁ g x≈y) }

.assoc-◽⋉ : ∀ {X Ys Zs Ws} {f : Zs ∗⇒∗ Ws} {g : Ys ∗⇒∗ Zs} {h : X ⇒∗ Ys}
          → (X ⇨∗ Ws) [ _⋉_ {Ys = Ys} {Ws} (_◽_ {Ys} {Zs} {Ws} f g) h ≈ _⋉_ {Ys = Zs} {Ws} f (_⋉_ {Ys = Ys} {Zs} g h) ]
assoc-◽⋉ {Ys = Ys} {Zs} {Ws} {f = f} {g} {h} {i} {j} i≈j with Ys _⟶_.⟨$⟩ j | cong₀ Ys i≈j | Zs _⟶_.⟨$⟩ j | cong₀ Zs i≈j | Ws _⟶_.⟨$⟩ j | cong₀ Ws i≈j | f ‼ j | cong₁ f i≈j | g ‼ j | cong₁ g i≈j | h ‼ j | cong₁ h i≈j
assoc-◽⋉ {f = f} {g} {h} {i} i≈j | ._ | ≣-refl | ._ | ≣-refl | ._ | ≣-refl | fj | ≡⇒∼ fi≡fj | gj | ≡⇒∼ gi≡gj | hj | ≡⇒∼ hi≡hj = 
  ≡⇒∼ (begin
    ((f ‼ i) ∘ (g ‼ i)) ∘ (h ‼ i)
  ↓⟨ ∘-resp-≡ (∘-resp-≡ fi≡fj gi≡gj) hi≡hj ⟩
    (fj ∘ gj) ∘ hj
  ↓⟨ assoc ⟩
    fj ∘ (gj ∘ hj)
  ∎)
  where 
  open Heterogeneous C hiding (≡⇒∼)
  open HomReasoning
