module Categories.2-Category.Categories where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.2-Category
open import Categories.Functor using (module Functor) renaming (id to idF; _∘_ to _∘F_)
open import Categories.Functor.Constant
open import Categories.FunctorCategory
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation
open import Categories.Product using (Product)

Categories : ∀ o ℓ e → 2-Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
Categories o ℓ e = record
  { Obj = Category o ℓ e
  ; _⇒_ = Functors
  ; id = λ {A} → Constant {D = Functors A A} idF
  ; —∘— = my-∘
  ; assoc = {!!}
  ; identityˡ = λ {A B} η → Heterogeneous.≡⇒∼ {C = Functors A B} {f = proj₂ η ∘₁ id} {proj₂ η} (Category.identityʳ B)
  ; identityʳ = λ {A B f g} η → Heterogeneous.≡⇒∼ {_} {_} {_} {C = Functors A B} {proj₁ f} {proj₁ g} {f = record {
                                                                                                η =
                                                                                                  λ X →
                                                                                                    Category._∘_ B (Functor.F₁ (proj₁ g) (Category.id A))
                                                                                                    (NaturalTransformation.η (proj₁ η) X);
                                                                                                commute = λ {a} {b} h → let open Category.HomReasoning B in begin
                    B [ B [ Functor.F₁ (proj₁ g) (Category.id A) ∘ NaturalTransformation.η (proj₁ η) b ] ∘ {!.Categories.NaturalTransformation.Core.F.F₁ (proj₁ f) (proj₁ g) h!} ]
                  ↓⟨ {!!} ⟩
                    B [ Functor.F₁ {!!} {!!} ∘ B [ Functor.F₁ (proj₁ g) (Category.id A) ∘ NaturalTransformation.η (proj₁ η) a ] ]
                  ∎ }
         } {proj₁ {_} {_} {_} {_} η} (Category.Equiv.trans B (Category.∘-resp-≡ˡ B (Functor.identity (proj₁ g))) (Category.identityˡ B))
  } 
  where
  my-∘ : {A B C : Category o ℓ e} → Bifunctor (Functors B C) (Functors A B) (Functors A C)
  my-∘ {A} {B} {C} = record
    { F₀ = uncurry′ _∘F_
    ; F₁ = uncurry′ _∘₀_
    ; identity = λ {Fs} → Category.Equiv.trans C (Category.identityʳ C) (Functor.identity (proj₁ Fs))
    ; homomorphism = λ {_ _ _ f g} → Category.Equiv.sym C (interchange {α = proj₁ g} {proj₂ g} {proj₁ f} {proj₂ f})
    ; F-resp-≡ = λ {_ _ f g} → my-resp {f = f} {g}
    }
    where
    PF = Product (Functors B C) (Functors A B)

    .my-resp : ∀ {F G} {f g : PF [ F , G ]} → PF [ f ≡ g ] → Functors A C [ uncurry′ _∘₀_ f ≡ uncurry _∘₀_ g ]
    my-resp {f = f₁ , f₂} {g₁ , g₂} (f₁≡g₁ , f₂≡g₂) = ∘₀-resp-≡ {f = f₁} {g₁} {f₂} {g₂} f₁≡g₁ f₂≡g₂