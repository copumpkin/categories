module Everything where

-- Categories
import Categories.Category

-- 2-categories
import Categories.2-Category

-- Adjunctions between functors
import Categories.Adjunction

-- The Agda Set category
import Categories.Agda

-- The arrow category construction on any category
import Categories.Arrow

-- Bifunctors (functors from a product category)
import Categories.Bifunctor

-- Natural transformations between bifunctors
import Categories.Bifunctor.NaturalTransformation

-- The category of (small) categories
import Categories.Categories

-- Closed categories
import Categories.Closed

-- Cocones
import Categories.Cocone

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

-- The diagonal functor (C -> C x C, or same thing with an arbitrary indexed product)
import Categories.Functor.Diagonal

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

-- The Grothendieck construction on categories (taking a Sets-valued functor and building a category containing all values)
import Categories.Grothendieck

-- The globe category, used for defining globular sets (with a presheaf on it)
import Categories.Globe

-- Globular sets
import Categories.GlobularSet

-- Left Kan extensions
import Categories.Lan

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

-- Free monad constructions for any functor
import Categories.Monad.Free

-- The Kleisli category for any monad
import Categories.Monad.Kleisli

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

-- Natural isomorphisms, defined as an isomorphism of natural transformations
import Categories.NaturalIsomorphism

-- Natural transformations
import Categories.NaturalTransformation


--------------------------------------------------------------------------------
-- Objects
--------------------------------------------------------------------------------

-- The coproduct of two objects
import Categories.Object.Coproduct

-- A category has all binary coproducts
import Categories.Object.Coproducts

-- An exponential object
import Categories.Object.Exponential

-- An initial object
import Categories.Object.Initial

-- The product of two objects
import Categories.Object.Product

-- All binary products
import Categories.Object.Products

-- Subobject classifiers (for topoi)
import Categories.Object.SubobjectClassifier

-- Terminal object
import Categories.Object.Terminal

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

-- Profunctors
import Categories.Profunctor

-- Pullbacks in a category
import Categories.Pullback

-- Pushouts in a category
import Categories.Pushout

-- All categories can have a slice category defined on them
import Categories.Slice

-- Utilities for gluing together commutative squares (and triangles)
import Categories.Square

-- The terminal category (a terminal object in the category of small categories)
import Categories.Terminal

-- A topos
import Categories.Topos
