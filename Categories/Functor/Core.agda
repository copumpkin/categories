{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level
open import Relation.Binary.PropositionalEquality.TrustMe
open import Categories.Support.PropositionalEquality
open import Categories.Support.EqReasoning

record Functor {o a o′ a′} (C : Category o a) (D : Category o′ a′) : Set (o ⊔ a ⊔ o′ ⊔ a′) where
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    .identity : ∀ {A} → F₁ (C.id {A}) ≣ D.id
    .homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → F₁ (C [ g ∘ f ]) ≣ D [ F₁ g ∘ F₁ f ]

  F-resp-≡ : ∀ {A B} {F G : C [ A , B ]} → F ≣ G → F₁ F ≣ F₁ G
  F-resp-≡ ≣-refl = ≣-refl

  -- XXX is this okay?
  identity-relevant : ∀ {A} → F₁ (C.id {A}) ≣ D.id
  identity-relevant {A} = trustMe

  abstract
    homomorphism-relevant : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                          → F₁ (C [ g ∘ f ]) ≣ D [ F₁ g ∘ F₁ f ]
    homomorphism-relevant = trustMe

  op : Functor C.op D.op
  op = record 
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = identity
    ; homomorphism = homomorphism
    }

record EasyFunctor {o a o′ a′ e′} (C : Category o a) (D : EasyCategory o′ a′ e′) : Set (o ⊔ a ⊔ o′ ⊔ a′ ⊔ e′) where
  private module C = Category C
  private module D = EasyCategory D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D ⟦ F₀ A , F₀ B ⟧

    .identity : ∀ {A} → D ⟦ F₁ (C.id {A}) ≡ D.id ⟧
    .homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → D ⟦ F₁ (C [ g ∘ f ]) ≡ D ⟦ F₁ g ∘ F₁ f ⟧ ⟧
  .F-resp-≡ : ∀ {A B} {F G : C [ A , B ]} → C [ F ≡ G ] → D ⟦ F₁ F ≡ F₁ G ⟧
  F-resp-≡ eq = D.demote _ _ (≣-cong F₁ eq)
  

  functor : Functor C (EASY D)
  functor = record 
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = D.promote _ _ identity
    ; homomorphism = D.promote _ _ homomorphism
    }

UNEASYF_WITH_ : ∀ {o a o′ a′ e′} {C : Category o a} {D : Category o′ a′} (F : Functor C D) (rel : EasyRel D e′) → EasyFunctor C (UNEASY D WITH rel)
UNEASYF F WITH rel = record
  { F₀ = F.F₀
  ; F₁ = F.F₁
  ; identity = rel.demote _ _ F.identity
  ; homomorphism = rel.demote _ _ F.homomorphism
  }
  where
  module F = Functor F
  module rel = EasyRel rel

Endofunctor : ∀ {o a} → Category o a → Set _
Endofunctor C = Functor C C

Contravariant : ∀ {o a o′ a′} (C : Category o a) (D : Category o′ a′) → Set _
Contravariant C D = Functor C.op D
  where module C = Category C

id : ∀ {o a} {C : Category o a} → Endofunctor C
id {C = C} = record 
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = refl
  ; homomorphism = refl
  }
  where open Category.Equiv C

infixr 9 _∘_

_∘_ : ∀ {o a} {o′ a′} {o′′ a′′} {C : Category o a} {D : Category o′ a′} {E : Category o′′ a′′} 
    → Functor D E → Functor C D → Functor C E
_∘_ {C = C} {D = D} {E = E} F G = record 
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = identity′
  ; homomorphism = homomorphism′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)

  .identity′ : ∀ {A} → E [ F₁ (G₁ (C.id {A})) ≡ E.id ]
  identity′ = begin
                F₁ (G₁ C.id)
              ≈⟨ F-resp-≡ G.identity ⟩
                F₁ D.id
              ≈⟨ F.identity ⟩
                E.id
              ∎
    where
    open SetoidReasoning E.hom-setoid

  .homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F₁ (G₁ (C [ g ∘ f ])) ≡ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ]
  homomorphism′ {f = f} {g = g} = begin
                                    F₁ (G₁ (C [ g ∘ f ]))
                                  ≈⟨ F-resp-≡ G.homomorphism ⟩
                                    F₁ (D [ G₁ g ∘ G₁ f ])
                                  ≈⟨ F.homomorphism ⟩
                                    (E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ])
                                  ∎
    where
    open SetoidReasoning E.hom-setoid

  .∘-resp-≡′ : ∀ {A B} {F G : C [ A , B ]} 
            → C [ F ≡ G ] → E [ F₁ (G₁ F) ≡ F₁ (G₁ G) ]
  ∘-resp-≡′ = λ x → F-resp-≡ (G-resp-≡ x)
