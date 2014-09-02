open import Categories.Category
import Categories.Functor as Fun
open import Categories.Monad
open import Categories.Object.BinaryCoproducts

import Categories.Normalise as Nm

module Categories.Monad.Coproduct {o ℓ e} (C : Category o ℓ e) (coprod : BinCoproducts C) where

open Category C
open Equiv

open BinCoproducts C coprod

module Internal where
  module +Reasoning = Nm.+Reasoning C coprod

  {- ----------------------------------------------------------------------------
     Functoriality of left
  ---------------------------------------------------------------------------- -}

  .left-id : ∀ {X Y} → left id ≡ id {X ∐ Y}
  left-id {X} {Y} = by computation {↑ X ⊎ ↑ Y} (#left #id) #id
    where
    open +Reasoning

  .left-∘ : ∀ {X Y Z W} {f : X ⇒ Y} {g : Y ⇒ Z} → left {C = W} (g ∘ f) ≡ left g ∘ left f
  left-∘ {X} {Y} {Z} {W} {f = f} {g} = 
    by computation {↑ X ⊎ ↑ W} 
         (#left (↑↑ g #∘ ↑↑ f)) 
         (#left (↑↑ g) #∘ #left (↑↑ f))
    where
    open +Reasoning

  .left-resp-≡ : ∀ {x y z} → {f g : x ⇒ y} → f ≡ g → left {C = z} f ≡ left {C = z} g
  left-resp-≡ {f = f} {g} p = 
    begin
      [ i₁ ∘ f , i₂ ∘ id ]
    ↓⟨ []-cong₂ (∘-resp-≡ʳ p) refl ⟩
      [ i₁ ∘ g , i₂ ∘ id ]
    ∎
    where
    open HomReasoning

  {- ----------------------------------------------------------------------------
     Functoriality of right
  ---------------------------------------------------------------------------- -}

  .right-id : ∀ {X Y} → right id ≡ id {X ∐ Y}
  right-id {X} {Y} = by computation {↑ X ⊎ ↑ Y} (#right #id) #id
    where
    open +Reasoning

  .right-∘ : ∀ {X Y Z W} {f : X ⇒ Y} {g : Y ⇒ Z} → right {A = W} (g ∘ f) ≡ right g ∘ right f
  right-∘ {X} {W = W} {f = f} {g} = by computation {↑ W ⊎ ↑ X} 
                                       (#right (↑↑ g #∘ ↑↑ f)) 
                                       (#right (↑↑ g) #∘ #right (↑↑ f))
    where
    open +Reasoning

  .right-resp-≡ : ∀ {x y z} → {f g : x ⇒ y} → f ≡ g → right {A = z} f ≡ right {A = z} g
  right-resp-≡ {f = f} {g} p =
    begin
      [ i₁ ∘ id , i₂ ∘ f ]
    ↓⟨ []-cong₂ refl (∘-resp-≡ʳ p) ⟩
      [ i₁ ∘ id , i₂ ∘ g ]
    ∎
    where
    open HomReasoning

  {- ----------------------------------------------------------------------------
     Left/Right functors
  ---------------------------------------------------------------------------- -}

  Left : Obj → Fun.Functor C C
  Left A =
   record
    { F₀ = λ X → X ∐ A
    ; F₁ = left
    ; identity = left-id
    ; homomorphism = left-∘
    ; F-resp-≡ = left-resp-≡
    }

  Right : Obj → Fun.Functor C C
  Right A =
   record
    { F₀ = _∐_ A
    ; F₁ = right
    ; identity = right-id
    ; homomorphism = right-∘
    ; F-resp-≡ = right-resp-≡
    }
    
private module I = Internal

{- ----------------------------------------------------------------------------
     Left/Right monads
---------------------------------------------------------------------------- -}

Left : Obj -> Monad C
Left c =
  record
    { F = I.Left c
    ; η = unit
    ; μ = join
    ; assoc = (λ {x} → by computation {#Left (#Left (#Left (↑ x)))}
                            (#join #∘ #left #join) 
                            (#join #∘ #join))
    ; identityˡ = λ {x} → by computation {#Left (↑ x)} (#join #∘ #left #i₁) #id
    ; identityʳ = λ {x} → by computation {#Left (↑ x)} (#join #∘ #i₁) #id
    }
  module Left where
    open I.+Reasoning

    #Left = λ x → x ⊎ ↑ c  

    unit = record { η = λ X → i₁
                  ; commute = λ {X} {Y} f → by computation {↑ X} {#Left (↑ Y)} 
                                    (#i₁ #∘ ↑↑ f) (#left (↑↑ f) #∘ #i₁)
                  }

    #join : ∀ {A} -> Term (#Left (#Left A)) (#Left A)
    #join = #[ #id , #i₂ ]

    join = record { η = λ X → [ id , i₂ ]
                  ; commute = λ {X} {Y} f → by computation {#Left (#Left (↑ X))}
                              (#join #∘ #left (#left (↑↑ f)))                                 
                              (#left (↑↑ f) #∘ #join)
                  }


Right : Obj -> Monad C
Right c =
  record
    { F = I.Right c
    ; η = unit
    ; μ = join
    ; assoc = (λ {x} → by computation {#Right (#Right (#Right (↑ x)))}
                            (#join #∘ #right #join) 
                            (#join #∘ #join))
    ; identityˡ = λ {x} → by computation {#Right (↑ x)} (#join #∘ #right #i₂) #id
    ; identityʳ = λ {x} → by computation {#Right (↑ x)} (#join #∘ #i₂) #id
    }
  module Right where
    open I.+Reasoning

    #Right = λ x → ↑ c ⊎ x

    unit = record { η = λ X → i₂
                  ; commute = λ {X} {Y} f → by computation {↑ X} {#Right (↑ Y)} 
                                    (#i₂ #∘ ↑↑ f) (#right (↑↑ f) #∘ #i₂)
                  }

    #join : ∀ {A} -> Term (#Right (#Right A)) (#Right A)
    #join = #[ #i₁ , #id ]

    join = record { η = λ X → [ i₁ , id ]
                  ; commute = λ {X} {Y} f → by computation {#Right (#Right (↑ X))}
                              (#join #∘ #right (#right (↑↑ f)))                                 
                              (#right (↑↑ f) #∘ #join)
                  }


