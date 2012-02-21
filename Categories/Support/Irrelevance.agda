module Categories.Support.Irrelevance where

import Level

postulate
  .irr : ∀ {a} {A : Set a} → .A → A
{-# BUILTIN IRRAXIOM irr #-}