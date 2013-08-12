module Categories.Support.Experimental where

open import Relation.Binary.PropositionalEquality.TrustMe

open import Categories.Support.PropositionalEquality

≣-relevant : ∀ {l} {A : Set l} {X Y : A} -> .(X ≣ Y) -> X ≣ Y
≣-relevant _ = trustMe

private
  ≣-coe : ∀ {a} {A B : Set a} → (A ≣ B) -> A -> B
  ≣-coe ≣-refl a = a

≣-subst′ : ∀ {a p} {A : Set a} → (P : A -> Set p) -> {x y : A} -> .(x ≣ y) -> P x -> P y
≣-subst′ P eq Px = ≣-coe (≣-relevant (≣-cong P eq)) Px
