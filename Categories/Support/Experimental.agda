module Categories.Support.Experimental where

open import Relation.Binary.PropositionalEquality.TrustMe

open import Categories.Support.PropositionalEquality

≣-relevant : ∀ {l} {A : Set l} {X Y : A} -> .(X ≣ Y) -> X ≣ Y
≣-relevant _ = trustMe
