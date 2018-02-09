{-# OPTIONS --universe-polymorphism #-}
open import Level hiding (suc; zero)
open import Categories.Category
module Categories.Power {o ℓ e : Level} (C : Category o ℓ e) where

open import Function using () renaming (id to idf)
open import Data.Nat using (ℕ; _+_; zero; suc; _≤?_)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; inject+; raise; zero; suc; #_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map) renaming ([_,_] to ⟦_,_⟧; [_,_]′ to ⟦_,_⟧′)
open import Function using (flip) renaming (_∘_ to _∙_)
open import Relation.Nullary.Decidable using (True)
open import Data.Vec.N-ary using (N-ary)

open import Categories.Bifunctor using (Bifunctor)
open import Categories.Functor using (Functor; module Functor)

module C = Category C

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
    { refl = λ {x} i → C.Equiv.refl
    ; sym = λ f i → C.Equiv.sym (f i)
    ; trans = λ f g i → C.Equiv.trans (f i) (g i)
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

_par_ : ∀ {I I′ J J′} (F : Hyperendo′ I I′) (G : Hyperendo′ J J′) → Hyperendo′ (I ⊎ J) (I′ ⊎ J′)
F par G = record
  { F₀ = λ xs → ⟦ F.F₀ (xs ∙ inj₁) , G.F₀ (xs ∙ inj₂) ⟧′
  ; F₁ = λ {A B} fs → ⟦ F.F₁ (fs ∙ inj₁) , G.F₁ (fs ∙ inj₂) ⟧
  ; identity = λ {A} → ⟦ F.identity , G.identity ⟧
  ; homomorphism = λ {A B C fs gs} → ⟦ F.homomorphism , G.homomorphism ⟧
  ; F-resp-≡ = λ {A B fs gs} fs≡gs → ⟦ F.F-resp-≡ (fs≡gs ∙ inj₁) , G.F-resp-≡ (fs≡gs ∙ inj₂) ⟧
  }
  where
  private module F = Functor F
  private module G = Functor G

flattenP : ∀ {D : Category o ℓ e} {n m} (F : Powerfunctor′ D (Fin n ⊎ Fin m)) → Powerfunctor′ D (Fin (n + m))
flattenP {n = n} {m = m} F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  private module F = Functor F
  pack = ⟦ inject+ m , raise n ⟧′

flattenHʳ : ∀ {I} {n m} (F : Hyperendo′ I (Fin n ⊎ Fin m)) → Hyperendo′ I (Fin (n + m))
flattenHʳ {n = n} {m} F = record
  { F₀ = λ As → F.F₀ As ∙ chops n
  ; F₁ = λ {As Bs} fs → F.F₁ fs ∙ chops n
  ; identity = F.identity ∙ chops n
  ; homomorphism = F.homomorphism ∙ chops n
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ fs≡gs ∙ chops n
  }
  where
  private module F = Functor F
  chops : (n : ℕ) → ∀ {m} (k : Fin (n + m)) → Fin n ⊎ Fin m
  chops 0 k = inj₂ k
  chops (suc n) zero = inj₁ zero
  chops (suc n) (suc k) = map suc idf (chops n k)


flattenH : ∀ {n m n′ m′} (F : Hyperendo′ (Fin n ⊎ Fin m) (Fin n′ ⊎ Fin m′)) → Hyperendo (n + m) (n′ + m′)
flattenH = flattenHʳ ∙ flattenP

_∥_ : ∀ {n n′ m m′} (F : Hyperendo n n′) (G : Hyperendo m m′) → Hyperendo (n + m) (n′ + m′)
F ∥ G = flattenH (F par G)

reduce′ : ∀ (H : Bifunctor C C C) {I J} (F : Powerendo′ I) (G : Powerendo′ J) → Powerendo′ (I ⊎ J)
reduce′ H {I} {J} F G = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = λ {As} → my-identity {As}
  ; homomorphism = λ {As Bs Cs fs gs} → my-homomorphism {fs = fs} {gs}
  ; F-resp-≡ = λ fs → H.F-resp-≡ (F.F-resp-≡ (fs ∙ inj₁) , G.F-resp-≡ (fs ∙ inj₂))
  }
  where
  private module L = Category (Exp (I ⊎ J)) 
  private module F = Functor F
  private module G = Functor G
  private module H = Functor H
  open L using () renaming (_≡_ to _≡≡_; _∘_ to _∘∘_)
  open C using (_≡_; _∘_)
  my-F₀ = λ As → H.F₀ ((F.F₀ (As ∙ inj₁)) , (G.F₀ (As ∙ inj₂)))
  my-F₁ : ∀ {As Bs} → L._⇒_ As Bs → C [ my-F₀ As , my-F₀ Bs ]
  my-F₁ {As} {Bs} fs = H.F₁ (F.F₁ (fs ∙ inj₁) , G.F₁ (fs ∙ inj₂))
  .my-identity : ∀ {As} → my-F₁ (L.id {As}) ≡ C.id
  my-identity {As} = begin
                        H.F₁ (F.F₁ (λ i → C.id {As (inj₁ i)}) , G.F₁ (λ i → C.id {As (inj₂ i)}))
                      ↓⟨ H.F-resp-≡ (F.identity , G.identity) ⟩
                        H.F₁ (C.id , C.id)
                      ↓⟨ H.identity ⟩
                        C.id
                      ∎
    where
    open C.HomReasoning
  .my-homomorphism : ∀ {As Bs Cs} {fs : L._⇒_ As Bs} {gs : L._⇒_ Bs Cs} → my-F₁ (gs ∘∘ fs) ≡ (my-F₁ gs ∘ my-F₁ fs)
  my-homomorphism {fs = fs} {gs} = 
    begin
      my-F₁ (gs ∘∘ fs)
    ↓⟨ H.F-resp-≡ (F.homomorphism , G.homomorphism) ⟩
      H.F₁ ((F.F₁ (gs ∙ inj₁) ∘ F.F₁ (fs ∙ inj₁)) , (G.F₁ (gs ∙ inj₂) ∘ G.F₁ (fs ∙ inj₂)))
    ↓⟨ H.homomorphism ⟩
      my-F₁ gs ∘ my-F₁ fs
    ∎
    where
    open C.HomReasoning

reduce : ∀ (H : Bifunctor C C C) {n m} (F : Powerendo n) (G : Powerendo m) → Powerendo (n + m)
reduce H F G = flattenP (reduce′ H F G)

flattenP-assocʳ : ∀ {n₁ n₂ n₃} (F : Powerendo′ (Fin n₁ ⊎ (Fin n₂ ⊎ Fin n₃))) → Powerendo ((n₁ + n₂) + n₃)
flattenP-assocʳ {n₁} {n₂} {n₃} F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  module F = Functor F
  pack = ⟦ inject+ n₃ ∙ inject+ n₂ , ⟦ inject+ n₃ ∙ raise n₁ , raise (n₁ + n₂) ⟧′ ⟧′

reduce2ʳ : ∀ (G : Bifunctor C C C) {n₁ n₂ n₃} (F₁ : Powerendo n₁) (F₂ : Powerendo n₂) (F₃ : Powerendo n₃) → Powerendo ((n₁ + n₂) + n₃)
reduce2ʳ G F₁ F₂ F₃ = flattenP-assocʳ (reduce′ G F₁ (reduce′ G F₂ F₃))

overlaps : ∀ {D E} (H : Bifunctor D D E) {I} (F G : Powerfunctor′ D I) → Powerfunctor′ E I
overlaps {D} {E} H {I} F G = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = λ {As} → my-identity {As}
  ; homomorphism = λ {As Bs Cs fs gs} → my-homomorphism {fs = fs} {gs}
  ; F-resp-≡ = λ fs → H.F-resp-≡ (F.F-resp-≡ fs , G.F-resp-≡ fs)
  }
  where
  private module L = Category (Exp I) 
  private module F = Functor F
  private module G = Functor G
  private module H = Functor H
  private module D = Category D
  private module E = Category E
  open L using () renaming (_≡_ to _≡≡_; _∘_ to _∘∘_)
  open E using (_≡_; _∘_)
  open D using () renaming (_∘_ to _∘D_)
  my-F₀ = λ As → H.F₀ (F.F₀ As , G.F₀ As)
  my-F₁ : ∀ {As Bs} → (Exp I) [ As , Bs ] → E [ my-F₀ As , my-F₀ Bs ]
  my-F₁ {As} {Bs} fs = H.F₁ (F.F₁ fs , G.F₁ fs)
  .my-identity : ∀ {As} → my-F₁ (L.id {As}) ≡ E.id
  my-identity {As} = begin
                        H.F₁ (F.F₁ (λ i → C.id {As i}) , G.F₁ (λ i → C.id {As i}))
                      ↓⟨ H.F-resp-≡ (F.identity , G.identity) ⟩
                        H.F₁ (D.id , D.id)
                      ↓⟨ H.identity ⟩
                        E.id
                      ∎
    where
    open E.HomReasoning
  .my-homomorphism : ∀ {As Bs Cs} {fs : (Exp I) [ As , Bs ]} {gs : (Exp I) [ Bs , Cs ]} → my-F₁ (gs ∘∘ fs) ≡ (my-F₁ gs ∘ my-F₁ fs)
  my-homomorphism {fs = fs} {gs} = 
    begin
      my-F₁ (gs ∘∘ fs)
    ↓⟨ H.F-resp-≡ (F.homomorphism , G.homomorphism) ⟩
      H.F₁ ((F.F₁ gs ∘D F.F₁ fs) , (G.F₁ gs ∘D G.F₁ fs))
    ↓⟨ H.homomorphism ⟩
      my-F₁ gs ∘ my-F₁ fs
    ∎
    where
    open E.HomReasoning

overlap2ʳ : ∀ (G : Bifunctor C C C) {n} (F₁ F₂ F₃ : Powerendo n) → Powerendo n
overlap2ʳ G F₁ F₂ F₃ = (overlaps {C} G F₁ (overlaps {C} G F₂ F₃))

select′ : ∀ {I} (i : I) → Powerendo′ I
select′ {I} i = record
  { F₀ = λ xs → xs i
  ; F₁ = λ fs → fs i
  ; identity = C.Equiv.refl
  ; homomorphism = C.Equiv.refl
  ; F-resp-≡ = λ eqs → eqs i
  }

select : ∀ m {n} {m<n : True (suc m ≤? n)} → Powerendo n
select m {n} {m<n} = select′ (#_ m {n} {m<n})

triv : (n : ℕ) → Hyperendo n n
triv n = record
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = λ _ → C.Equiv.refl
  ; homomorphism = λ _ → C.Equiv.refl
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
  module F = Functor F

unaryH : (F : Functor C C) → Hyperendo 1 1
unaryH F = record
  { F₀ = λ As → F.F₀ ∙ As
  ; F₁ = λ fs → F.F₁ ∙ fs
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs → F.F-resp-≡ ∙ fs≡gs
  }
  where
  module F = Functor F

nullary : (X : C.Obj) → Powerendo 0
nullary X = record
  { F₀ = λ _ → X
  ; F₁ = λ _ → C.id
  ; identity = C.Equiv.refl
  ; homomorphism = C.Equiv.sym C.identityˡ
  ; F-resp-≡ = λ _ → C.Equiv.refl
  }

nullaryH : (X : C.Obj) → Hyperendo 0 1
nullaryH X = record
  { F₀ = λ _ _ → X
  ; F₁ = λ _ _ → C.id
  ; identity = λ _ → C.Equiv.refl
  ; homomorphism = λ _ → C.Equiv.sym C.identityˡ
  ; F-resp-≡ = λ _ _ → C.Equiv.refl
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
  module F = Functor F

binaryH : (F : Bifunctor C C C) → Hyperendo 2 1
binaryH F = record
  { F₀ = λ As _ → F.F₀ (As zero , As (suc zero))
  ; F₁ = λ fs _ → F.F₁ (fs zero , fs (suc zero))
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs _ → F.F-resp-≡ (fs≡gs zero , fs≡gs (suc zero))
  }
  where
  module F = Functor F

hyp : ∀ {n} (F : Powerendo n) → Hyperendo n 1
hyp F = record
  { F₀ = λ As _ → F.F₀ As
  ; F₁ = λ fs _ → F.F₁ fs
  ; identity = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≡ = λ fs≡gs _ → F.F-resp-≡ fs≡gs
  }
  where
  module F = Functor F

private
  curryⁿ : ∀ n {a b} {A : Set a} {B : Set b} → ((Fin n → A) → B) → N-ary n A B
  curryⁿ zero f = f (λ ())
  curryⁿ (suc n) {A = A} f = λ x → curryⁿ n (f ∙ addon x)
    where
    addon : A → (Fin n → A) → Fin (suc n) → A
    addon x _ zero = x
    addon _ g (suc i) = g i

plex′ : ∀ {J I} → (J → Powerendo′ I) → Hyperendo′ I J
plex′ Fs = record
  { F₀ = flip (Functor.F₀ ∙ Fs)
  ; F₁ = flip (λ j → Functor.F₁ (Fs j))
  ; identity = λ j → Functor.identity (Fs j)
  ; homomorphism = λ j → Functor.homomorphism (Fs j)
  ; F-resp-≡ = flip (λ j → Functor.F-resp-≡ (Fs j))
  }

plex : ∀ {n} {I} → N-ary n (Powerendo′ I) (Hyperendo′ I (Fin n))
plex {n} = curryⁿ n plex′

widenˡ : ∀ (l : ℕ) {n} (F : Powerendo n) → Powerendo (l + n)
widenˡ l F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  private module F = Functor F
  pack = raise l

widenʳ : ∀ (r : ℕ) {n} (F : Powerendo n) → Powerendo (n + r)
widenʳ r F = record
  { F₀ = λ As → F.F₀ (As ∙ pack)
  ; F₁ = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity = λ {As} → F.identity
  ; homomorphism = λ {As Bs Cs fs gs} → F.homomorphism
  ; F-resp-≡ = λ {As Bs fs gs} fs≡gs → F.F-resp-≡ (fs≡gs ∙ pack)
  }
  where
  private module F = Functor F
  pack = inject+ r
