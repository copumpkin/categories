-- Actually, we're cheating (for expediency); this is
-- Symmetric Rig, not just Rig.
module Categories.RigCategory where

open import Level
open import Data.Fin renaming (zero to 0F; suc to sucF)
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Functor
open import Categories.Monoidal
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Braided.Helpers
open import Categories.Monoidal.Symmetric
open import Categories.Monoidal.Helpers
open import Categories.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘₀_; _∘₁_; _∘ˡ_; _∘ʳ_; NaturalTransformation) renaming (_≡_ to _≡ⁿ_; id to idⁿ)

-- first round of setting up, just for defining the NaturalIsomorphisms
-- of Rig.  Next one will be for the equalities.
module BimonoidalHelperFunctors {o ℓ e} {C : Category o ℓ e} 
  {M⊎ M× : Monoidal C} (B⊎ : Braided M⊎) (B× : Braided M×) where

  private
    module C = Category C
    module M⊎ = Monoidal M⊎
    module M× = Monoidal M×
    module B⊎ = Braided B⊎
    module B× = Braided B×

  module h⊎ = MonoidalHelperFunctors C M⊎.⊗ M⊎.id
  module h× = MonoidalHelperFunctors C M×.⊗ M×.id
  module b⊎ = BraidedHelperFunctors C M⊎.⊗ M⊎.id
  module b× = BraidedHelperFunctors C M×.⊗ M×.id

  module br⊎ = b⊎.Braiding M⊎.identityˡ M⊎.identityʳ M⊎.assoc B⊎.braid
  module br× = b×.Braiding M×.identityˡ M×.identityʳ M×.assoc B×.braid
  
  import Categories.Power.NaturalTransformation
  private module PowNat = Categories.Power.NaturalTransformation C
  open PowNat hiding (module C)

  -- for convenience of multiple of the larger equations, define
  -- shorthands for 3 and 4 variables
  x⊗z : Powerendo 3
  x⊗z = select 0 h×.⊗₂ select 2
  
  z⊗x : Powerendo 3
  z⊗x = (select 2) h×.⊗₂ (select 0)

  z⊗y : Powerendo 3
  z⊗y = select 2 h×.⊗₂ select 1

  y⊗z : Powerendo 3
  y⊗z = select 1 h×.⊗₂ select 2

  x : Powerendo 4
  x = select 0

  y : Powerendo 4
  y = select 1

  z : Powerendo 4
  z = select 2

  w : Powerendo 4
  w = select 3

  -- combinations of 3 variables
  x⊗[y⊕z] : Powerendo 3
  x⊗[y⊕z] = h×.x h×.⊗ (h⊎.x⊗y)

  x⊗[z⊕y] : Powerendo 3
  x⊗[z⊕y] = h×.x h×.⊗ h⊎.y⊗x

  [x⊕y]⊗z : Powerendo 3
  [x⊕y]⊗z = (h⊎.x⊗y) h×.⊗ h×.x

  z⊗[x⊕y] : Powerendo 3
  z⊗[x⊕y] = (select 2) h×.⊗₂ ((select 0) h⊎.⊗₂ (select 1))
  
  [x⊗y]⊕[x⊗z] : Powerendo 3
  [x⊗y]⊕[x⊗z] = (select 0 h×.⊗₂ select 1) h⊎.⊗₂ (select 0 h×.⊗₂ select 2) 

  [x⊗z]⊕[y⊗z] : Powerendo 3
  [x⊗z]⊕[y⊗z] = (select 0 h×.⊗₂ select 2) h⊎.⊗₂ (select 1 h×.⊗₂ select 2)

  [z⊗x]⊕[z⊗y] : Powerendo 3
  [z⊗x]⊕[z⊗y] = z⊗x h⊎.⊗₂ z⊗y

  [x⊗z]⊕[x⊗y] : Powerendo 3
  [x⊗z]⊕[x⊗y] = x⊗z h⊎.⊗₂ (select 0 h×.⊗₂ select 1)
  
  x⊗0 : Powerendo 1
  x⊗0 = h⊎.x h×.⊗ h⊎.id↑

  0⊗x : Powerendo 1
  0⊗x = h⊎.id↑ h×.⊗ h⊎.x

  0↑ : Powerendo 1
  0↑ = widenˡ 1 h⊎.id↑

  xy : Powerendo 4
  xy = widenʳ 2 h×.x⊗y
  
  yz : Powerendo 4
  yz = select 1 h×.⊗₂ select 2
  
  xw : Powerendo 4
  xw = select 0 h×.⊗₂ select 3

  yw : Powerendo 4
  yw = select 1 h×.⊗₂ select 3

  zw : Powerendo 4
  zw = select 2 h×.⊗₂ select 3

  z⊕w : Powerendo 4
  z⊕w = widenˡ 2 h⊎.x⊗y

  -- 0 variables!
  0₀ : Powerendo 0
  0₀ = h⊎.id↑
  
  0⊗0 : Powerendo 0
  0⊗0 = 0₀ h×.⊗ 0₀

  0⊕0 : Powerendo 0
  0⊕0 = 0₀ h⊎.⊗ 0₀

  1₀ : Powerendo 0
  1₀ = h×.id↑

  -- 1 variable + 0
  A0 : Powerendo 1
  A0 = h×.x h×.⊗ 0₀

  0A : Powerendo 1
  0A = 0₀ h×.⊗ h×.x

  -- 2 variables + 0
  0[A⊕B] : Powerendo 2
  0[A⊕B] = (widenʳ 2 0₀) h×.⊗₂ h⊎.x⊗y

  0A⊕0B : Powerendo 2
  0A⊕0B = ( (widenʳ 2 0₀ h×.⊗₂ select 0) h⊎.⊗₂ (widenʳ 2 0₀ h×.⊗₂ select 1) )

  -- like Laplaza, use concatenation for ⊗ to make things easier to read
  -- also ⊗ binds more tightly, so skip those parens

  -- combinations of 4 variables
  [x⊕[y⊕z]]w : Powerendo 4
  [x⊕[y⊕z]]w = h⊎.x⊗[y⊗z] h×.⊗ h⊎.x

  xw⊕[y⊕z]w : Powerendo 4
  xw⊕[y⊕z]w = (x h×.⊗₂ w) h⊎.⊗₂ ((y h⊎.⊗₂ z) h×.⊗₂ w)

  xw⊕[yw⊕zw] : Powerendo 4
  xw⊕[yw⊕zw] = (x h×.⊗₂ w) h⊎.⊗₂ ((y h×.⊗₂ w) h⊎.⊗₂ (z h×.⊗₂ w))

  [xw⊕yw]⊕zw : Powerendo 4
  [xw⊕yw]⊕zw = ((x h×.⊗₂ w) h⊎.⊗₂ (y h×.⊗₂ w)) h⊎.⊗₂ (z h×.⊗₂ w)

  [[x⊕y]⊕z]w : Powerendo 4
  [[x⊕y]⊕z]w = h⊎.[x⊗y]⊗z h×.⊗ h⊎.x

  [x⊕y]w⊕zw : Powerendo 4
  [x⊕y]w⊕zw = ((x h⊎.⊗₂ y) h×.⊗₂ w) h⊎.⊗₂ (z h×.⊗₂ w)

  x[y[z⊕w]] : Powerendo 4
  x[y[z⊕w]] = x h×.⊗₂ (y h×.⊗₂ (z h⊎.⊗₂ w))

  x[yz⊕yw] : Powerendo 4
  x[yz⊕yw] = x h×.⊗₂ ((y h×.⊗₂ z) h⊎.⊗₂ (y h×.⊗₂ w))

  x[yz]⊕x[yw] : Powerendo 4
  x[yz]⊕x[yw] = (x h×.⊗₂ (y h×.⊗₂ z)) h⊎.⊗₂ (x h×.⊗₂ (y h×.⊗₂ w))

  [xy][z⊕w] : Powerendo 4
  [xy][z⊕w] = (x h×.⊗₂ y) h×.⊗₂ (z h⊎.⊗₂ w)

  [xy]z⊕[xy]w : Powerendo 4
  [xy]z⊕[xy]w = let xy = (x h×.⊗₂ y) in (xy h×.⊗₂ z) h⊎.⊗₂ (xy h×.⊗₂ w)
  
  module SRig (S⊎ : Symmetric B⊎) (S× : Symmetric B×)
    (distribₗ : NaturalIsomorphism x⊗[y⊕z] [x⊗y]⊕[x⊗z])
    (distribᵣ : NaturalIsomorphism [x⊕y]⊗z [x⊗z]⊕[y⊗z])
    (annₗ : NaturalIsomorphism 0⊗x 0↑)
    (annᵣ : NaturalIsomorphism x⊗0 0↑) where

    open NaturalIsomorphism distribₗ using () renaming (F⇒G to dₗ)
    open NaturalIsomorphism distribᵣ using () renaming (F⇒G to dᵣ)
    open NaturalIsomorphism annₗ using () renaming (F⇒G to aₗ)
    open NaturalIsomorphism annᵣ using () renaming (F⇒G to aᵣ)

    dₗ-over : ∀ {n} (F₁ F₂ F₃ : Powerendo n) → NaturalTransformation (F₁ h×.⊗₂ (F₂ h⊎.⊗₂ F₃)) ((F₁ h×.⊗₂ F₂) h⊎.⊗₂ (F₁ h×.⊗₂ F₃))
    dₗ-over F₁ F₂ F₃ = dₗ ∘ʳ plex {3} F₁ F₂ F₃
    
    dᵣ-over : ∀ {n} (F₁ F₂ F₃ : Powerendo n) → NaturalTransformation ((F₁ h⊎.⊗₂ F₂) h×.⊗₂ F₃) ((F₁ h×.⊗₂ F₃) h⊎.⊗₂ (F₂ h×.⊗₂ F₃))
    dᵣ-over F₁ F₂ F₃ = dᵣ ∘ʳ plex {3} F₁ F₂ F₃

    aₗ-over : ∀ {n} (F₁ : Powerendo n) → NaturalTransformation ((widenʳ n 0₀) h×.⊗₂ F₁) (widenʳ n 0₀)
    aₗ-over F₁ = aₗ ∘ʳ plex {1} F₁ 

    aᵣ-over : ∀ {n} (F₁ : Powerendo n) → NaturalTransformation (F₁ h×.⊗₂ (widenʳ n 0₀)) (widenʳ n 0₀)
    aᵣ-over F₁ = aᵣ ∘ʳ plex {1} F₁ 

    uₗ⊕-over : ∀ {n} (F₁ : Powerendo n) → NaturalTransformation ((widenʳ n 0₀) h⊎.⊗₂ F₁) F₁
    uₗ⊕-over F₁ = (NaturalIsomorphism.F⇒G M⊎.identityˡ) ∘ʳ plex {1} F₁

    uᵣ⊗-over : ∀ {n} (F₁ : Powerendo n) → NaturalTransformation (F₁ h×.⊗₂ (widenʳ n 1₀)) F₁
    uᵣ⊗-over F₁ = (NaturalIsomorphism.F⇒G M×.identityʳ) ∘ʳ plex {1} F₁

    s⊗-over : ∀ {n} (F₁ F₂ : Powerendo n) → NaturalTransformation (F₁ h×.⊗₂ F₂) (F₂ h×.⊗₂ F₁)
    s⊗-over F₁ F₂ = (NaturalIsomorphism.F⇒G B×.braid) ∘ʳ plex {2} F₁ F₂

    -- these are all for 3 variables
    Bxz : NaturalTransformation x⊗z z⊗x
    Bxz = br×.B-over (select 0) (select 2)

    Byz : NaturalTransformation y⊗z z⊗y
    Byz = br×.B-over (select 1) (select 2)
  
    Bxz⊕Byz : NaturalTransformation [x⊗z]⊕[y⊗z] [z⊗x]⊕[z⊗y]
    Bxz⊕Byz = Bxz h⊎.⊗ⁿ′ Byz

    B[x⊕y]z : NaturalTransformation [x⊕y]⊗z z⊗[x⊕y]
    B[x⊕y]z = br×.B-over (widenʳ 1 h⊎.x⊗y) (select 2)

    dᵣABC : NaturalTransformation [x⊕y]⊗z [x⊗z]⊕[y⊗z]
    dᵣABC = dᵣ-over (select 0) (select 1) (select 2)

    dₗABC : NaturalTransformation x⊗[y⊕z] [x⊗y]⊕[x⊗z]
    dₗABC = dₗ-over (select 0) (select 1) (select 2)

    dₗACB : NaturalTransformation x⊗[z⊕y] [x⊗z]⊕[x⊗y]
    dₗACB = dₗ-over (select 0) (select 2) (select 1)
    
    dₗCAB : NaturalTransformation z⊗[x⊕y] [z⊗x]⊕[z⊗y]
    dₗCAB = dₗ-over (select 2) (select 0) (select 1)

    1⊗Byz : NaturalTransformation x⊗[y⊕z] x⊗[z⊕y]
    1⊗Byz = reduceN M×.⊗ h×.id₂ (br⊎.B-over (select 0) (select 1))

    B[x⊗y][x⊗z] : NaturalTransformation [x⊗y]⊕[x⊗z] [x⊗z]⊕[x⊗y]
    B[x⊗y][x⊗z] = br⊎.B-over (widenʳ 1 h×.x⊗y) x⊗z

    -- these are all for 4 variables
    dᵣA[B⊕C]D : NaturalTransformation [x⊕[y⊕z]]w xw⊕[y⊕z]w
    dᵣA[B⊕C]D = dᵣ-over (select 0) (widenʳ 1 (widenˡ 1 h⊎.x⊗y)) (select 3)

    dᵣBCD : NaturalTransformation (widenˡ 1 [x⊕y]⊗z) (widenˡ 1 [x⊗z]⊕[y⊗z])
    dᵣBCD = dᵣ-over (select 1) (select 2) (select 3)

    id03 : NaturalTransformation xw xw
    id03 = idⁿ

    id23 : NaturalTransformation zw zw
    id23 = idⁿ

    idx : NaturalTransformation x x
    idx = idⁿ
    
    idw : NaturalTransformation w w
    idw = idⁿ
    
    1⊗dᵣBCD : NaturalTransformation xw⊕[y⊕z]w xw⊕[yw⊕zw]
    1⊗dᵣBCD = overlapN M⊎.⊗ id03 dᵣBCD

    assocˡAD-BD-CD : NaturalTransformation xw⊕[yw⊕zw] [xw⊕yw]⊕zw
    assocˡAD-BD-CD = br⊎.α₂-over xw yw zw

    αˡABC⊗1 : NaturalTransformation [x⊕[y⊕z]]w [[x⊕y]⊕z]w
    αˡABC⊗1 = overlapN M×.⊗ (br⊎.α₂-over (select 0) (select 1) (select 2)) idw

    dᵣ[A⊕B]CD : NaturalTransformation [[x⊕y]⊕z]w [x⊕y]w⊕zw
    dᵣ[A⊕B]CD = dᵣ-over (widenʳ 2 h⊎.x⊗y) (select 2) (select 3)

    dᵣABD⊗1 : NaturalTransformation [x⊕y]w⊕zw [xw⊕yw]⊕zw
    dᵣABD⊗1 = overlapN M⊎.⊗ (dᵣ-over (select 0) (select 1) (select 3)) id23

    1A⊗dₗBCD : NaturalTransformation x[y[z⊕w]] x[yz⊕yw]
    1A⊗dₗBCD = overlapN M×.⊗ idx (dₗ-over y z w)

    dₗA[BC][BD] : NaturalTransformation x[yz⊕yw] x[yz]⊕x[yw]
    dₗA[BC][BD] = dₗ-over x yz yw

    αABC⊕αABD : NaturalTransformation x[yz]⊕x[yw] [xy]z⊕[xy]w
    αABC⊕αABD = overlapN M⊎.⊗ (br×.α₂-over x y z) (br×.α₂-over x y w)

    αAB[C⊕D] : NaturalTransformation x[y[z⊕w]] [xy][z⊕w]
    αAB[C⊕D] = br×.α₂-over x y z⊕w

    dₗ[AB]CD : NaturalTransformation [xy][z⊕w] [xy]z⊕[xy]w
    dₗ[AB]CD = dₗ-over xy z w
 
    dₗ0AB : NaturalTransformation 0[A⊕B] 0A⊕0B
    dₗ0AB = dₗ-over (widenʳ 2 0₀) (select 0) (select 1)

    aₗA⊕aₗB : NaturalTransformation 0A⊕0B (widenʳ 2 0⊕0)
    aₗA⊕aₗB = overlapN M⊎.⊗ (aₗ-over (select 0)) (aₗ-over (select 1))

    -- a bit weird, but the widening is needed
    uˡ0 : NaturalTransformation (widenʳ 2 0⊕0) (widenʳ 2 0₀) 
    uˡ0 = uₗ⊕-over (widenʳ 2 0₀)

    aᵣA : NaturalTransformation A0 0↑
    aᵣA = aᵣ-over (select 0)
 
    aₗA : NaturalTransformation 0A (widenʳ 1 0₀)
    aₗA = aₗ-over (select 0)

    s⊗A0 : NaturalTransformation A0 0A
    s⊗A0 = s⊗-over (select 0) 0↑

record RigCategory {o ℓ e} {C : Category o ℓ e} 
  {M⊎ M× : Monoidal C} {B⊎ : Braided M⊎} (S⊎ : Symmetric B⊎)
   {B× : Braided M×} (S× : Symmetric B×) : Set (o ⊔ ℓ ⊔ e) where

  open BimonoidalHelperFunctors B⊎ B×

  field
    distribₗ : NaturalIsomorphism x⊗[y⊕z] [x⊗y]⊕[x⊗z]
    distribᵣ : NaturalIsomorphism [x⊕y]⊗z [x⊗z]⊕[y⊗z]
    annₗ : NaturalIsomorphism 0⊗x 0↑
    annᵣ : NaturalIsomorphism x⊗0 0↑

  open SRig S⊎ S× distribₗ distribᵣ annₗ annᵣ

  -- need II, IX, X, XV
  -- choose I, IV, VI, XI, XIII, XIX, XXIII and (XVI, XVII)
  field
    laplazaI : dₗACB ∘₁ 1⊗Byz ≡ⁿ B[x⊗y][x⊗z] ∘₁ dₗABC
    laplazaII : Bxz⊕Byz ∘₁ dᵣABC ≡ⁿ dₗCAB ∘₁ B[x⊕y]z
    laplazaIV : dᵣABD⊗1 ∘₁ (dᵣ[A⊕B]CD ∘₁ αˡABC⊗1) ≡ⁿ assocˡAD-BD-CD ∘₁ (1⊗dᵣBCD ∘₁ dᵣA[B⊕C]D)
    laplazaVI : dₗ[AB]CD ∘₁ αAB[C⊕D] ≡ⁿ αABC⊕αABD ∘₁ (dₗA[BC][BD] ∘₁ 1A⊗dₗBCD)
    -- laplazaIX
    laplazaX : aₗ-over 0₀ ≡ⁿ aᵣ-over 0₀
    laplazaXI : aₗ-over (h⊎.x⊗y) ≡ⁿ uˡ0 ∘₁ (aₗA⊕aₗB ∘₁ dₗ0AB)
    laplazaXIII : uᵣ⊗-over 0₀ ≡ⁿ aₗ-over 1₀
    laplazaXV : aᵣA ≡ⁿ aₗA ∘₁ s⊗A0
    -- laplazaXVI
    -- laplazaXVII
    -- laplazaXVIX
    -- laplazaXXIII

