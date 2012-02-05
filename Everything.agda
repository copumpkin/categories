module Everything where

-- Categories
import Categories.Category

-- 2-categories
-- XXX need to finish the last 3 laws
import Categories.2-Category

-- The strict 2-category of categories
-- XXX laws not proven yet
-- import Categories.2-Category.Categories

-- Adjunctions between functors
import Categories.Adjunction

-- The Agda Set category
import Categories.Agda

-- The fact that one version of it is cocomplete
import Categories.Agda.ISetoids.Cocomplete

-- The arrow category construction on any category
import Categories.Arrow

-- Bifunctors (functors from a product category)
import Categories.Bifunctor

-- Natural transformations between bifunctors
import Categories.Bifunctor.NaturalTransformation

-- The category of (small) categories
import Categories.Categories

-- Cat has products
import Categories.Categories.Products

-- Closed categories
import Categories.Closed

-- Cocones
import Categories.Cocone

-- The category of cocones under a diagram (functor)
import Categories.Cocones

-- Coends
import Categories.Coend

-- Coequalizers
import Categories.Coequalizer

-- Colimits
import Categories.Colimit

-- Comma categories
import Categories.Comma

-- Comonads, defined directly (not as monads on the opposite category)
import Categories.Comonad

-- The cofree construction that gives a comonad for any functor
import Categories.Comonad.Cofree

-- Cones
import Categories.Cone

-- The category of cones over a diagram (functor)
import Categories.Cones

-- A coherent equivalence relation over the objects of a category
import Categories.Congruence

-- Discrete categories (they only have objects and identity morphisms)
import Categories.Discrete

-- Ends
import Categories.End

-- Enriched categories
import Categories.Enriched

-- Equalizers
import Categories.Equalizer

-- Strong equivalence
import Categories.Equivalence.Strong

-- Fibrations
import Categories.Fibration

-- Free category on a graph
import Categories.Free

-- The free category construction is a functor from Gph to Cat
import Categories.Free.Functor

-- Functors
import Categories.Functor

-- F-algebra (TODO: maybe the module should be renamed)
import Categories.Functor.Algebra

-- The category of F-algebras of a functor
import Categories.Functor.Algebras

-- An F-coalgebra
import Categories.Functor.Coalgebra

-- Constant functor
import Categories.Functor.Constant

-- The category of F-coalgebras of a functor
import Categories.Functor.Coalgebras

-- The diagonal functor (C → C × C, or same thing with an arbitrary indexed product)
import Categories.Functor.Diagonal

-- Strong functor equivalence
-- XXX doesn't seem to work because of the double negative in Full?
-- import Categories.Functor.Equivalence.Strong

-- The hom functor, mapping pairs of objects to the morphisms between them
import Categories.Functor.Hom

-- Monoidal functors (similar to Haskell's Applicative class)
import Categories.Functor.Monoidal

-- Products as functors
import Categories.Functor.Product

-- Properties of general functors
import Categories.Functor.Properties

-- Representable functors
import Categories.Functor.Representable

-- Functor categories (of functors between two categories and natural transformations between them)
import Categories.FunctorCategory

-- The category of graphs and graph homomorphisms (Gph)
import Categories.Graphs

-- The underlying graph of a category (forgetful functor Cat ⇒ Gph)
import Categories.Graphs.Underlying

-- The Grothendieck construction on categories (taking a Sets-valued functor and building a category containing all values)
import Categories.Grothendieck

-- The globe category, used for defining globular sets (with a presheaf on it)
import Categories.Globe

-- Globular sets
import Categories.GlobularSet

-- Left Kan extensions
import Categories.Lan

-- Small categories exist as large categories too
import Categories.Lift

-- Limits
import Categories.Limit

-- Monads, defined as simple triples of a functor and two natural transformations
import Categories.Monad

-- A monad algebra
import Categories.Monad.Algebra

-- The category of all algebras of a monad
import Categories.Monad.Algebras

-- The Eilenberg-Moore category for any monad
import Categories.Monad.EilenbergMoore

-- The Kleisli category for any monad
import Categories.Monad.Kleisli

-- Strong monads
import Categories.Monad.Strong

-- Monoidal categories, with an associative bi(endo)functor and an identity object
import Categories.Monoidal

-- A braided monoidal category (one that gives you a swap operation, but isn't quite commutative)
import Categories.Monoidal.Braided

-- A cartesian monoidal category (monoidal category whose monoid is the product with a terminal object)
import Categories.Monoidal.Cartesian

-- Closed monoidal categories, which are simply monoidal categories that are
-- also closed, such that the laws "fit"
import Categories.Monoidal.Closed

-- Both of the above. Separated into its own module because we can do many
-- interesting things with them.
import Categories.Monoidal.CartesianClosed

-- Simple definitions about morphisms, such as mono, epi, and iso
import Categories.Morphisms

-- Cartesian morphisms (used mostly for fibrations)
import Categories.Morphism.Cartesian

-- Families of morphisms indexed by a set
import Categories.Morphism.Indexed

-- Natural isomorphisms, defined as an isomorphism of natural transformations
import Categories.NaturalIsomorphism

-- Natural transformations
import Categories.NaturalTransformation

import Categories.DinaturalTransformation

-- Properties of the opposite category
import Categories.Opposite

--------------------------------------------------------------------------------
-- Objects
--------------------------------------------------------------------------------

-- The coproduct of two objects
import Categories.Object.Coproduct

-- A category has all binary coproducts
import Categories.Object.BinaryCoproducts

-- A category has all finite coproducts
import Categories.Object.Coproducts

-- An exponential object
import Categories.Object.Exponential

-- A choice of B^A for a given B and any A
import Categories.Object.Exponentiating

-- B^— is adjoint to its opposite
import Categories.Object.Exponentiating.Adjunction

-- B^— as a functor
import Categories.Object.Exponentiating.Functor

-- A family of objects indexed by a set
import Categories.Object.Indexed

-- An initial object
import Categories.Object.Initial

-- The product of two objects
import Categories.Object.Product

-- The usual nice constructions on products, conditionalized on existence
import Categories.Object.Product.Morphisms

-- All binary products
import Categories.Object.BinaryProducts

-- Products of a nonempty list of objects and the ability to reassociate them massively
import Categories.Object.BinaryProducts.N-ary

-- All finite products
import Categories.Object.Products
import Categories.Object.Products.Properties

-- Products of a list of objects and the ability to reassociate them massively
import Categories.Object.Products.N-ary

-- The product of a family of objects
import Categories.Object.IndexedProduct

-- All products of indexed families
import Categories.Object.IndexedProducts

-- Subobject classifiers (for topoi)
import Categories.Object.SubobjectClassifier

-- Terminal object
import Categories.Object.Terminal

-- A^1 and 1^A always exist
import Categories.Object.Terminal.Exponentials

-- A chosen 1^A exists
import Categories.Object.Terminal.Exponentiating

-- A×1 always exists
import Categories.Object.Terminal.Products

-- Zero object (initial and terminal)
import Categories.Object.Zero

-- A category containing n copies of objects/morphisms/equalities of another category
import Categories.Power

-- Demonstrations that Power categories are the same as functors from discrete categories
import Categories.Power.Functorial

-- Natural transformations for functors to/from power categories
import Categories.Power.NaturalTransformation

-- A preorder gives rise to a category
import Categories.Preorder

-- A presheaf (functor from C^op to V)
import Categories.Presheaf

-- The category of presheaves (a specific functor category)
import Categories.Presheaves

-- The product of two categories
import Categories.Product
import Categories.Product.Properties

-- Projection functors from a product category to its factors
import Categories.Product.Projections

-- Profunctors
import Categories.Profunctor

-- Pullbacks in a category
import Categories.Pullback

-- Pushouts in a category
import Categories.Pushout

-- All categories can have a slice category defined on them
import Categories.Slice

-- Utilities for gluing together commutative squares (and triangles)
-- (and other common patterns of equational reasoning)
import Categories.Square

-- The terminal category (a terminal object in the category of small categories)
import Categories.Terminal

-- A topos
import Categories.Topos

-- The Yoneda lemma
import Categories.Yoneda
