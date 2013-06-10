module Categories.Operations where

open import Level

data ∘Spec {l r a} (Left : Set l) (Right : Set r) (Answer : Set a) : Set (suc (l ⊔ r ⊔ a)) where
  COMPOSES_ : (compose : Left → Right → Answer) → ∘Spec Left Right Answer

infixr 9 _∘_

_∘_ : ∀ {l r a} {Left : Set l} {Right : Set r} {Answer : Set a}
        {{spec : ∘Spec Left Right Answer}} → Left → Right → Answer
_∘_ {{COMPOSES compose}} = compose
