{-# OPTIONS --universe-polymorphism #-}

module Categories.Support.SetoidPi where

open import Level
open import Function as Fun using (_on_)
open import Relation.Binary as B using () renaming (_=[_]⇒_ to _=[_]⇒₀_; _⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)
open import Relation.Binary.Indexed.Heterogeneous as I using (_=[_]⇒_)
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions as SF using (_⟶_) renaming (_⟨$⟩_ to _⟨$⟩₀_; cong to cong₀)
open Setoid using () renaming (Carrier to Carrier₀; _≈_ to _[_≈_])

_⟶[_,_] : ∀ {cf ℓf} (From : Setoid cf ℓf) (ct ℓt : Level) → Set (cf ⊔ ℓf ⊔ suc (ct ⊔ ℓt))
From ⟶[ ct , ℓt ] = From ⟶ set→setoid (Setoid ct ℓt)

------------------------------------------------------------------------
-- Indexed binary relations
------------------------------------------------------------------------

record IndexedSetoid {i iℓ} (I : Set i) (_∼_ : B.Rel I iℓ) c ℓ : Set (suc (i ⊔ iℓ ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : I.IRel Carrier ℓ
    .isEquivalence : I.IsIndexedEquivalence Carrier _≈_
    -- NOTE one more field, see resp below

  -- no irrelevant opens ☹
  -- .open I.IsEquivalence isEquivalence public
  private
    module E = I.IsIndexedEquivalence
  .refl : I.Reflexive Carrier _≈_
  refl = E.refl isEquivalence
  .sym : I.Symmetric Carrier _≈_
  sym = E.sym isEquivalence
  .trans : I.Transitive Carrier _≈_
  trans = E.trans isEquivalence

  .reflexive : ∀ {i} → _≡_ ⊆ (_≈_ {i})
  reflexive = E.reflexive isEquivalence

  -- conversion to regular setoids by evaluating at an index
  _at_ : I → Setoid c ℓ
  _at_ i = record
    { Carrier = Carrier i
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl = E.refl isEquivalence
      ; sym = E.sym isEquivalence
      ; trans = E.trans isEquivalence
      }
    }

  -- XXX ideally i should redo the resp stuff and promotion and everything
  -- with the proper setoid of setoids under equivalence, but first i didn't
  -- make it yet and second OH MY GOD                         ─xplat
  Resp-Type = _∼_ =[ _at_ ]⇒₀ _≡_ {A = Setoid c ℓ}
  field
    .resp          : Resp-Type

resp-per : ∀ {c ℓ} {C₁ C₂ : Set c} {_≈₁_ : B.Rel C₁ ℓ} {_≈₂_ : B.Rel C₂ ℓ} {equiv₁ : B.IsEquivalence _≈₁_} {equiv₂ : B.IsEquivalence _≈₂_} → C₁ ≡ C₂ → _≈₁_ ≅ _≈₂_ → _≡_ {A = Setoid c ℓ} record {Carrier = C₁; _≈_ = _≈₁_; isEquivalence = equiv₁} record {Carrier = C₂; _≈_ = _≈₂_; isEquivalence = equiv₂}
resp-per _≡_.refl ≅-refl = _≡_.refl

.resp-per′ : ∀ {c ℓ} (S T : Setoid c ℓ) → (Carrier₀ S ≡ Carrier₀ T) → (Setoid._≈_ S ≅ Setoid._≈_ T) → S ≡ T
resp-per′ S T = resp-per {equiv₁ = Setoid.isEquivalence S} {equiv₂ = Setoid.isEquivalence T}

open IndexedSetoid using (_at_)

weaken : ∀ {c ℓ} → Setoid c ℓ → ∀ {i iℓ} {I : Set i} {_∼_ : B.Rel I iℓ} → IndexedSetoid I _∼_ c ℓ
weaken S {I = I} {_∼_} = record
  { Carrier = Fun.const S.Carrier
  ; _≈_ = S._≈_
  ; isEquivalence = record { refl = S.refl; sym = S.sym; trans = S.trans }
  ; resp = Fun.const _≡_.refl
  }
  where module S = Setoid S

{-
-- this definition is unusable because agda spins in circles trying to infer
-- ct and ℓt before it will extract any information from f's type, but f's
-- type is the only thing it can infer them from... test is below ☹
_[$]_ : ∀ {cf ℓf ct ℓt} {From : Setoid cf ℓf} → (From ⟶[ ct , ℓt ]) → Carrier From → Set ct
f [$] x = Carrier (f ⟨$⟩₀ x)

.test : ∀ {cf ℓf ct ℓt} {From : Setoid cf ℓf} (To : From ⟶[ ct , ℓt ]) (x : Carrier From) → (_[$]_ {ct = ct}{ℓt = ℓt} To x) → Set ℓt
test = {!!}
-}

-- i think this approach would work beautifully with regular setoids, but
-- with irrelevant setoids the type of cong can't depend on localize
--                                                          ─ xplat

-- .localize : ∀ {cf ℓf ct ℓt} {From : Setoid cf ℓf} (To : From ⟶[ ct , ℓt ]) {x y : Carrier₀ From} → From [ x ≈ y ] → B.REL (Carrier₀ (To ⟨$⟩₀ x)) (Carrier₀ (To ⟨$⟩₀ y)) ℓt
-- localize To {x} x≈y with To ⟨$⟩₀ x | cong₀ To x≈y
-- localize To x≈y | ._ | _≡_.refl = Setoid._≈_ (To ⟨$⟩₀ _)

-- ... so it's on to yet another annoying heterogeneous equality type
module SetoidHetero {cf ℓf} (From : Setoid cf ℓf) (ct ℓt : Level) (To : From ⟶[ ct , ℓt ]) where
  I = Carrier₀ From
  To$ = _⟨$⟩₀_ To
  To$C = Fun._∘_ Carrier₀ (_⟨$⟩₀_ To)

  localize′ : ∀ {S T : Setoid ct ℓt} → (S ≡ T) → B.REL (Carrier₀ S) (Carrier₀ T) ℓt
  -- localize′ {S} {T} S≡T
  localize′ {S} _≡_.refl = Setoid._≈_ S

  localize : ∀ {x y : I} → (To$ x ≡ To$ y) → B.REL (To$C x) (To$C y) ℓt
  localize {x} {y} To$x≡To$y with To$ y
  localize {x} _≡_.refl | ._ = Setoid._≈_ (To$ x)

  data _≈∗_ {S T : Setoid ct ℓt} (x : Carrier₀ S) : (y : Carrier₀ T) → Set (suc (ct ⊔ ℓt)) where
    locally : (S≡T : S ≡ T)
      {y : Carrier₀ T} (x≈y : localize′ S≡T x y) →
      _≈∗_ {S} {T} x y

  _≈⋆_ : {iˣ iʸ : I} → B.REL (To$C iˣ) (To$C iʸ) (suc (ct ⊔ ℓt))
  _≈⋆_ {iˣ} {iʸ} = _≈∗_ {To$ iˣ} {To$ iʸ}

asIndexed : ∀ {cf ℓf} ct ℓt {From : Setoid cf ℓf} → (From ⟶[ ct , ℓt ]) → IndexedSetoid (Carrier₀ From) (Setoid._≈_ From) ct (suc (ct ⊔ ℓt))
asIndexed ct ℓt {From} To = record
  { Carrier = To$C
  ; _≈_ = _≈⋆_
  ; isEquivalence = record
    { refl = my-refl
    ; sym = my-sym
    ; trans = my-trans
    }
  ; resp = λ {i j} i∼j → resp-per′ (fake-at i) (fake-at j) (resp-helper i∼j) (resp-helper₂ i∼j)
  }
  where
  open SetoidHetero _ ct ℓt To

  .my-refl : I.Reflexive To$C _≈⋆_
  my-refl {i} {x} = locally {To$ i} _≡_.refl ((Setoid.refl (To$ i)))

  .sym-helper : ∀ i j (To$i≡To$j : To$ i ≡ To$ j) (x : To$C i) (y : To$C j) (x≈y : localize′ To$i≡To$j x y) → localize′ (PE.sym To$i≡To$j) y x
  sym-helper i j To$i≡To$j x y with To$ j
  sym-helper i j _≡_.refl x y | ._ = Setoid.sym (To$ i)

  .my-sym : I.Symmetric To$C _≈⋆_
  my-sym {i} {j} {x} {y} (locally To$i≡To$j x≈y) = locally (PE.sym To$i≡To$j) (sym-helper i j To$i≡To$j x y x≈y)

  .trans-helper : ∀ i j k (To$i≡To$j : To$ i ≡ To$ j) (To$j≡To$k : To$ j ≡ To$ k) (x : To$C i) (y : To$C j) (z : To$C k) (x≈y : localize′ To$i≡To$j x y) (y≈z : localize′ To$j≡To$k y z) → localize′ (PE.trans To$i≡To$j To$j≡To$k) x z
  trans-helper i j k To$i≡To$j To$j≡To$k x y z with To$ j | To$ k
  trans-helper i j k _≡_.refl _≡_.refl x y z | ._ | ._ = Setoid.trans (To$ i)

  .my-trans : I.Transitive To$C _≈⋆_
  my-trans (locally To$i≡To$j x≈y) (locally To$j≡To$k y≈z) = locally (PE.trans To$i≡To$j To$j≡To$k) (trans-helper _ _ _ To$i≡To$j To$j≡To$k _ _ _ x≈y y≈z)

  .resp-helper : ∀ {i j} → From [ i ≈ j ] → To$C i ≡ To$C j
  resp-helper i∼j = PE.cong Carrier₀ (cong₀ To i∼j)

  .resp-helper₃ : (S T : Setoid ct ℓt) → S ≡ T → _≈∗_ {S} {S} ≅ _≈∗_ {T} {T}
  resp-helper₃ S .S _≡_.refl = ≅-refl 

  .resp-helper₂ : ∀ {i j} → From [ i ≈ j ] → _≈⋆_ {i} {i} ≅ _≈⋆_ {j} {j}
  resp-helper₂ {i} {j} i∼j = resp-helper₃ (To$ i) (To$ j) (cong₀ To i∼j)

  fake-at : ∀ i → Setoid ct (suc (ct ⊔ ℓt))
  fake-at i = record
    { Carrier = To$C i
    ; _≈_ = _≈⋆_ {i} {i}
    ; isEquivalence = record
      { refl = my-refl
      ; sym = my-sym
      ; trans = my-trans
      }
    }

------------------------------------------------------------------------
-- Functions which preserve equality

record Π {f₁ f₂ t₁ t₂}
         (From : Setoid f₁ f₂)
         (To : IndexedSetoid (Carrier₀ From) (Setoid._≈_ From) t₁ t₂) :
         Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  open I using (_=[_]⇒_)
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : (x : Carrier₀ From) → IndexedSetoid.Carrier To x
    .cong : Setoid._≈_ From =[ _⟨$⟩_ ]⇒ IndexedSetoid._≈_ To

open Π public

Π′ : ∀ {cf ℓf} (ct ℓt : Level) (From : Setoid cf ℓf) (To : From ⟶[ ct , ℓt ]) → Set (cf ⊔ ℓf ⊔ suc (ct ⊔ ℓt))
Π′ ct ℓt From To = Π From (asIndexed ct ℓt To)

-- Pis that 'just happen' to be independent, instead of being necessarily so.

infixr 0 _⟶Π_

_⟶Π_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Set _
From ⟶Π To = Π From (weaken To)

-- Identity and composition.

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶Π A
id = record { _⟨$⟩_ = Fun.id; cong = Fun.id }

infixr 9 _∙′_

_∙′_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : Setoid c₁ c₂} →
      B ⟶Π C → A ⟶Π B → A ⟶Π C
f ∙′ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }

infixr 9 _[_○_]

-- XXX this shouldn't need B, but it can't be inferred from f's type
_[_○_] : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
           {b₁ b₂} (B : Setoid b₁ b₂)
           {c₁ c₂} (C : IndexedSetoid _ (Setoid._≈_ B) c₁ c₂) →
         (A ⟶Π B) → IndexedSetoid _ _ c₁ c₂
B [ C ○ f ] = record
  { Carrier = Fun._∘_ C.Carrier (_⟨$⟩_ f)
  ; _≈_ = C._≈_
  ; isEquivalence = record { refl = C.refl; sym = C.sym; trans = C.trans }
  ; resp = Fun._∘_ C.resp (cong f)
  }
  where module C = IndexedSetoid C

-- PROPER.  well, halfway.
infixr 9 _∙_

_∙_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : IndexedSetoid _ _ c₁ c₂} →
      (f : Π B C) → (g : A ⟶Π B) → Π A (B [ C ○ g ])
f ∙ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }

-- Constant equality-preserving function.

const : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
          {b₁ b₂} {B : Setoid b₁ b₂} →
        Carrier₀ B → A ⟶Π B
const {B = B} b = record
  { _⟨$⟩_ = Fun.const b
  ; cong  = Fun.const (Setoid.refl B)
  }

------------------------------------------------------------------------
-- Function setoids

-- Dependent.

setoid : ∀ {f₁ f₂ t₁ t₂}
         (From : Setoid f₁ f₂) →
         IndexedSetoid (Carrier₀ From) (Setoid._≈_ From) t₁ t₂ →
         Setoid _ _
setoid From To = record
  { Carrier       = Π From To
  ; _≈_           = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  ; isEquivalence = record
    { refl  = λ {f} → cong f
    ; sym   = λ f∼g x∼y → To.sym (f∼g (From.sym x∼y))
    ; trans = λ f∼g g∼h x∼y → To.trans (f∼g From.refl) (g∼h x∼y)
    }
  }
  where
  open module From = Setoid      From using () renaming (_≈_ to _≈₁_)
  open module To = IndexedSetoid To   using () renaming (_≈_ to _≈₂_)

