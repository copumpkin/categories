{-# OPTIONS --universe-polymorphism #-}

open import Level

module Categories.Categories.Products (o ℓ e : Level) where

open import Categories.Category
open import Categories.Categories

import Categories.Object.Products
open Categories.Object.Products (Categories o ℓ e)

open import Categories.Product
import Categories.Product.Projections
import Categories.Product.Properties

open import Categories.Terminal

private
    import Categories.Object.Product
    open Categories.Object.Product (Categories o ℓ e)
        renaming (Product to ProductObject)
    
    product : 
        {A B : Category o ℓ e}
        → ProductObject A B
    
    product {A}{B} = record
        { A×B       = Product A B
        ; π₁        = ∏₁
        ; π₂        = ∏₂
        ; ⟨_,_⟩     = _※_
        ; commute₁  = λ {C}{f}{g}    → ※-commute₁  {A = C}{f}{g}
        ; commute₂  = λ {C}{f}{g}    → ※-commute₂  {A = C}{f}{g}
        ; universal = λ {C}{f}{g}{i} → ※-universal {A = C}{f}{g}{i}
        } where
            open Categories.Product.Projections A B
            open Categories.Product.Properties  A B

products : Products
products = record
    { terminal = One {o}{ℓ}{e}
    ; binary = record
        { product = λ {A}{B} → product {A}{B}
        }
    }
