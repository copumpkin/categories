{-# OPTIONS --universe-polymorphism #-}
module Categories.Monoidal.Cartesian where

open import Data.Product using (proj₁; proj₂) renaming (_×_ to _×₀_)
open import Data.Fin using (zero)

open import Categories.Category
open import Categories.Monoidal
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Object.Products.Properties
  renaming (module Properties to ProductProperties)
open import Categories.Object.Terminal
open import Categories.Bifunctor using (Bifunctor)
import Categories.Morphisms
open import Categories.Square
import Categories.Monoidal.Cartesian.Pentagon as Pentagon

Cartesian : ∀ {o ℓ e} (C : Category o ℓ e) → Products C → Monoidal C
Cartesian C Ps = record
  { ⊗ = ⊗
  ; id = ⊤
  ; identityˡ = record
    { F⇒G = record
      { η = λ X → π₂
      ; commute = λ f → commute₂
      }
    ; F⇐G = record
      { η = λ X → ⟨ ! , id ⟩
      ; commute = λ f → unitˡ-natural
      }
    ; iso = λ X → _≅_.iso unitˡ
    }
  ; identityʳ = record
    { F⇒G = record
      { η = λ X → π₁
      ; commute = λ f → commute₁
      }
    ; F⇐G = record
      { η = λ X → ⟨ id , ! ⟩
      ; commute = λ f → unitʳ-natural
      }
    ; iso = λ X → _≅_.iso unitʳ
    }
  ; assoc = record
    { F⇒G = record
      { η = λ X → assocˡ
      ; commute = λ f → assocˡ∘⁂
      }
    ; F⇐G = record
      { η = λ X → assocʳ
      ; commute = λ f → assocʳ∘⁂
      }
    ; iso = λ X → record
      { isoˡ = Iso.isoʳ (_≅_.iso ×-assoc)
      ; isoʳ = Iso.isoˡ (_≅_.iso ×-assoc)
      }
    }
  ; triangle = λ {X} → triangle {X}
  ; pentagon = pentagon
  }
  where
  open Categories.Morphisms C
  open Category C
  open Products Ps renaming (terminal to T₀; binary to P₀)
  open ProductProperties C Ps
  open Terminal T₀ using (⊤; !; !-unique; !-unique₂)

  open BinaryProducts P₀
  open Pentagon.Law C P₀ using (pentagon)

  ⊗ : Bifunctor C C C
  ⊗ = record
    { F₀ = λ p → proj₁ p × proj₂ p
    ; F₁ = λ x → proj₁ x ⁂ proj₂ x
    ; identity = identity
    ; homomorphism = Equiv.sym ⁂∘⁂
    ; F-resp-≡ = λ {A B F G} x → F-resp-≡ {A} {B} {F} {G} x
    }
    where
    .identity : ∀ {A : Obj ×₀ Obj} → (id {proj₁ A} ⁂ id {proj₂ A}) ≡ id 
    identity = universal (id-comm {f = π₁}) (id-comm {f = π₂})
    
    .F-resp-≡ : ∀ {A B F G} F≡G → _
    F-resp-≡ {F = F} {G} x = ⟨⟩-cong₂ (∘-resp-≡ˡ (proj₁ x)) (∘-resp-≡ˡ (proj₂ x))

  -- The implicit x is actually used implicitly by the rest of the expression, so don't take it out,
  -- or Agda will complain about something referring to something to which it has no access.
  -- The connection between the mentioned x and the rest of the type is given by the caller way up
  -- there, so if that were not using these the triangle and pentagon laws would be yellow.
  .triangle : ∀ {x} → first π₁ ≡ second π₂ ∘ assocˡ
  triangle = 
    begin
      first π₁
    ↓⟨ ⟨⟩-congʳ identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ↑⟨ ⟨⟩-congʳ commute₂ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↑⟨ second∘⟨⟩ ⟩
      second π₂ ∘ assocˡ
    ∎
    where
    open HomReasoning
    open Equiv    
