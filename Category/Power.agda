{-# OPTIONS --universe-polymorphism #-}
open import Support using (Level)
open import Category using (Category)
module Category.Power {o ℓ e : Level} (C : Category o ℓ e) where

open import Support
open import Support.Nat
open import Support.FinSet
open import Category
open import Category.Bifunctor using (Bifunctor)
open import Category.Functor using (Functor)

module C = Category.Category C

Exp : (I : Set) → Category o ℓ e
Exp I = record
  { Obj = I → C.Obj
  ; _⇒_ = λ x y → (i : I) → C [ x i , y i ]
  ; _≡_ = λ f g → (i : I) → C [ f i ≡ g i ]
  ; _∘_ = λ f g i → C [ f i ∘ g i ]
  ; id = λ {x} i → C.id
  ; assoc = λ {A} {B} {C'} {D} {f} {g} {h} i → C.assoc
  ; identityˡ = λ {A} {B} {f} i → C.identityˡ
  ; identityʳ = λ {A} {B} {f} i → C.identityʳ
  ; equiv = record
    { refl = λ {x} i → IsEquivalence.refl C.equiv
    ; sym = λ f i → IsEquivalence.sym C.equiv (f i)
    ; trans = λ f g i → IsEquivalence.trans C.equiv (f i) (g i)
    }
  ; ∘-resp-≡ = λ f≡g h≡i x → C.∘-resp-≡ (f≡g x) (h≡i x)
  }
  
Power : (n : ℕ) → Category o ℓ e
Power n = Exp (Fin n)

Powerfunctor′ : (D : Category o ℓ e) (I : Set) → Set (e ⊔ ℓ ⊔ o)
Powerfunctor′ D I = Functor (Exp I) D

Powerfunctor : (D : Category o ℓ e) (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Powerfunctor D n = Powerfunctor′ D (Fin n)

Powerendo′ : (I : Set) → Set (e ⊔ ℓ ⊔ o)
Powerendo′ I = Powerfunctor′ C I

Powerendo : (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Powerendo n = Powerfunctor C n

Hyperendo : (n m : ℕ) → Set (e ⊔ ℓ ⊔ o)
Hyperendo n m = Functor (Power n) (Power m)

Hyperendo′ : (I J : Set) → Set (e ⊔ ℓ ⊔ o)
Hyperendo′ I J = Functor (Exp I) (Exp J)

_par_ : ∀ {I I′ J J′} (F : Hyperendo′ I I′) (G : Hyperendo′ J J′) → Hyperendo′ (Either I J) (Either I′ J′)
F par G = record
  { F₀ = λ xs → either₀ (F.F₀ (xs ∙ inl)) (G.F₀ (xs ∙ inr))
  ; F₁ = λ {A B} fs → either′ (F.F₁ (fs ∙ inl)) (G.F₁ (fs ∙ inr))
  ; identity = λ {A} → either′ F.identity G.identity
  ; homomorphism = λ {A B C fs gs} → either′ F.homomorphism G.homomorphism
  ; F-resp-≡ = λ {A B fs gs} fs≡gs → either′ (F.F-resp-≡ (fs≡gs ∙ inl)) (G.F-resp-≡ (fs≡gs ∙ inr))
  }
  where
  private module F = Category.Functor.Functor F
  private module G = Category.Functor.Functor G

flattenP : ∀ {D : Category o ℓ e} {n m} (F : Powerfunctor′ D (Either (Fin n) (Fin m))) → Powerfunctor′ D (Fin (n + m))
flattenP {n = n} {m = m} F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  private module F = Category.Functor.Functor F
  pack = either₀ (widen-+ m) (shift n)

flattenHʳ : ∀ {I} {n m} (F : Hyperendo′ I (Either (Fin n) (Fin m))) → Hyperendo′ I (Fin (n + m))
flattenHʳ {n = n} {m} F = record
  { F₀ = λ As → F.F₀ As ∙ _chops_ n
  ; F₁ = λ {As Bs} fs → F.F₁ fs ∙ _chops_ n
  ; identity = F.identity ∙ _chops_ n
  ; homomorphism = F.homomorphism ∙ _chops_ n
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ fs≡gs ∙ _chops_ n
  }
  where
  private module F = Category.Functor.Functor F

flattenH : ∀ {n m n′ m′} (F : Hyperendo′ (Either (Fin n) (Fin m)) (Either (Fin n′) (Fin m′))) → Hyperendo (n + m) (n′ + m′)
flattenH = flattenHʳ ∙ flattenP

_∥_ : ∀ {n n′ m m′} (F : Hyperendo n n′) (G : Hyperendo m m′) → Hyperendo (n + m) (n′ + m′)
F ∥ G = flattenH (F par G)

reduce′ : ∀ (H : Bifunctor C C C) {I J} (F : Powerendo′ I) (G : Powerendo′ J) → Powerendo′ (Either I J)
reduce′ H {I} {J} F G = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = λ {As} → my-identity {As}
  ; homomorphism = λ {As Bs Cs fs gs} → my-homomorphism {fs = fs} {gs}
  ; F-resp-≡ = λ fs → H.F-resp-≡ (F.F-resp-≡ (fs ∙ inl) , G.F-resp-≡ (fs ∙ inr))
  }
  where
  private module L = Category.Category (Exp (Either I J)) 
  private module F = Category.Functor.Functor F
  private module G = Category.Functor.Functor G
  private module H = Category.Functor.Functor H
  open L using () renaming (_≡_ to _≡≡_; _∘_ to _∘∘_)
  open C using (_≡_; _∘_)
  my-F₀ = λ As → H.F₀ ((F.F₀ (As ∙ inl)) , (G.F₀ (As ∙ inr)))
  my-F₁ : ∀ {As Bs} → L._⇒_ As Bs → C [ my-F₀ As , my-F₀ Bs ]
  my-F₁ {As} {Bs} fs = H.F₁ (F.F₁ (fs ∙ inl) , G.F₁ (fs ∙ inr))
  .my-identity : ∀ {As} → my-F₁ (L.id {As}) ≡ C.id
  my-identity {As} = begin
                        H.F₁ (F.F₁ (λ i → C.id {As (inl i)}) , G.F₁ (λ i → C.id {As (inr i)}))
                      ≈⟨ H.F-resp-≡ (F.identity , G.identity) ⟩
                        H.F₁ (C.id , C.id)
                      ≈⟨ H.identity ⟩
                        C.id
                      ∎
    where
    open SetoidReasoning C.hom-setoid
  .my-homomorphism : ∀ {As Bs Cs} {fs : L._⇒_ As Bs} {gs : L._⇒_ Bs Cs} → my-F₁ (gs ∘∘ fs) ≡ (my-F₁ gs ∘ my-F₁ fs)
  my-homomorphism {fs = fs} {gs} = 
    begin
      my-F₁ (gs ∘∘ fs)
    ≈⟨ H.F-resp-≡ (F.homomorphism , G.homomorphism) ⟩
      H.F₁ ((F.F₁ (gs ∙ inl) ∘ F.F₁ (fs ∙ inl)) , (G.F₁ (gs ∙ inr) ∘ G.F₁ (fs ∙ inr)))
    ≈⟨ H.homomorphism ⟩
      my-F₁ gs ∘ my-F₁ fs
    ∎
    where
    open SetoidReasoning C.hom-setoid 

reduce : ∀ (H : Bifunctor C C C) {n m} (F : Powerendo n) (G : Powerendo m) → Powerendo (n + m)
reduce H F G = flattenP (reduce′ H F G)

flattenP-assocʳ : ∀ {n₁ n₂ n₃} (F : Powerendo′ (Either (Fin n₁) (Either (Fin n₂) (Fin n₃)))) → Powerendo ((n₁ + n₂) + n₃)
flattenP-assocʳ {n₁} {n₂} {n₃} F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  module F = Category.Functor.Functor F
  pack = either₀ (widen-+ n₃ ∙ widen-+ n₂) (either₀ (widen-+ n₃ ∙ shift n₁) (shift (n₁ + n₂)))

reduce2ʳ : ∀ (G : Bifunctor C C C) {n₁ n₂ n₃} (F₁ : Powerendo n₁) (F₂ : Powerendo n₂) (F₃ : Powerendo n₃) → Powerendo ((n₁ + n₂) + n₃)
reduce2ʳ G F₁ F₂ F₃ = flattenP-assocʳ (reduce′ G F₁ (reduce′ G F₂ F₃))

triv : (n : ℕ) → Hyperendo n n
triv n = record
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = λ _ → IsEquivalence.refl C.equiv
  ; homomorphism = λ _ → IsEquivalence.refl C.equiv
  ; F-resp-≡ = λ x → x
  }

pad : ∀ (l r : ℕ) {n m} (F : Hyperendo n m) → Hyperendo ((l + n) + r) ((l + m) + r)
pad l r F = (triv l ∥ F) ∥ triv r

padˡ : ∀ (l : ℕ) {n m} (F : Hyperendo n m) → Hyperendo (l + n) (l + m)
padˡ l F = triv l ∥ F

padʳ : ∀ (r : ℕ) {n m} (F : Hyperendo n m) → Hyperendo (n + r) (m + r)
padʳ r F = F ∥ triv r

unary : (F : Functor C C) → Powerendo 1
unary F = record
  { F₀ = λ As → F.F₀ (As zero)
  ; F₁ = λ fs → F.F₁ (fs zero)
  ; identity = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ (fs≡gs zero)
  }
  where
  module F = Category.Functor.Functor F

unaryH : (F : Functor C C) → Hyperendo 1 1
unaryH F = record
  { F₀ = λ As → F.F₀ ∙ As
  ; F₁ = λ fs → F.F₁ ∙ fs
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ ∙ fs≡gs
  }
  where
  module F = Category.Functor.Functor F

nullary : (X : C.Obj) → Powerendo 0
nullary X = record
  { F₀ = λ _ → X
  ; F₁ = λ _ → C.id
  ; identity = IsEquivalence.refl C.equiv
  ; homomorphism = IsEquivalence.sym C.equiv C.identityˡ
  ; F-resp-≡ = λ _ → IsEquivalence.refl C.equiv
  }

nullaryH : (X : C.Obj) → Hyperendo 0 1
nullaryH X = record
  { F₀ = λ _ _ → X
  ; F₁ = λ _ _ → C.id
  ; identity = λ _ → IsEquivalence.refl C.equiv
  ; homomorphism = λ _ → IsEquivalence.sym C.equiv C.identityˡ
  ; F-resp-≡ = λ _ _ → IsEquivalence.refl C.equiv
  }

binary : (F : Bifunctor C C C) → Powerendo 2
binary F = record
  { F₀ = λ As → F.F₀ (As zero , As (suc zero))
  ; F₁ = λ fs → F.F₁ (fs zero , fs (suc zero))
  ; identity = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ (fs≡gs zero , fs≡gs (suc zero))
  }
  where
  module F = Category.Functor.Functor F

binaryH : (F : Bifunctor C C C) → Hyperendo 2 1
binaryH F = record
  { F₀ = λ As _ → F.F₀ (As zero , As (suc zero))
  ; F₁ = λ fs _ → F.F₁ (fs zero , fs (suc zero))
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs _ → F.F-resp-≡ (fs≡gs zero , fs≡gs (suc zero))
  }
  where
  module F = Category.Functor.Functor F

hyp : ∀ {n} (F : Powerendo n) → Hyperendo n 1
hyp F = record
  { F₀ = λ As _ → F.F₀ As
  ; F₁ = λ fs _ → F.F₁ fs
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs _ → F.F-resp-≡ fs≡gs
  }
  where
  module F = Category.Functor.Functor F
