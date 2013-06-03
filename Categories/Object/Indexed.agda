{-# OPTIONS --universe-polymorphism #-}
open import Categories.Category

module Categories.Object.Indexed {o a c} (C : Category o a) (B : Set c) where

open Category C

Dust = B → Obj

_!_ : Dust → B → Obj
d ! b = d b
