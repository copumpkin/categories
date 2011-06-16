{-# OPTIONS --universe-polymorphism #-}
module Categories.Support.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public using () renaming (_≡_ to _≣_; refl to ≣-refl; trans to ≣-trans; sym to ≣-sym; cong to ≣-cong)