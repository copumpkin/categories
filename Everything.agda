module Everything where

-- Categories
import Category

-- Adjunctions between functors
import Category.Adjunction

-- The arrow category construction on any category
import Category.Arrow

-- Bifunctors (functors from a product category)
import Category.Bifunctor

-- Closed categories
import Category.Closed

-- Cocones
import Category.Cocone

-- Coends
import Category.Coend

-- Coequalizers
import Category.Coequalizer

-- Colimits
import Category.Colimit

-- Comma categories
import Category.Comma

-- Comonads, defined directly (not as monads on the opposite category)
import Category.Comonad

-- The cofree construction that gives a comonad for any functor
import Category.Comonad.Cofree

-- Cones
import Category.Cone

-- Ends
import Category.End

-- Equalizers
import Category.Equalizer

-- Functors
import Category.Functor

-- F-algebra (TODO: maybe the module should be renamed)
import Category.Functor.Algebra

-- The hom functor, mapping pairs of objects to the morphisms between them
import Category.Functor.Hom

-- Monoidal functors (similar to Haskell's Applicative class)
import Category.Functor.Monoidal

-- Representable functors (to the category of Agda or Agda setoids; haven't yet decided)
import Category.Functor.Representable

-- Limits
import Category.Limit

-- Monads, defined as simple triples of a functor and two natural transformations
import Category.Monad

-- A monad algebra
import Category.Monad.Algebra

-- The category of all algebras of a monad
import Category.Monad.Algebras

-- The Eilenberg-Moore category for any monad
import Category.Monad.EilenbergMoore

-- Free monad constructions for any functor
import Category.Monad.Free

-- The Kleisli category for any monad
import Category.Monad.Kleisli

-- Monoidal categories, with an associative bi(endo)functor and an identity object
import Category.Monoidal

-- A braided monoidal category (one that gives you a swap operation, but isn't quite commutative)
import Category.Monoidal.Braided

-- A cartesian monoidal category (monoidal category whose monoid is the product with a terminal object)
import Category.Monoidal.Cartesian

-- Closed monoidal categories, which are simply monoidal categories that are
-- also closed, such that the laws "fit"
import Category.Monoidal.Closed

-- Both of the above. Separated into its own module because we can do many
-- interesting things with them.
import Category.Monoidal.CartesianClosed


-- Simple definitions about morphisms, such as mono, epi, and iso
import Category.Morphisms

-- Natural isomorphisms, defined as an isomorphism of natural transformations
import Category.NaturalIsomorphism

-- Natural transformations
import Category.NaturalTransformation


--------------------------------------------------------------------------------
-- Objects
--------------------------------------------------------------------------------

-- The coproduct of two objects
import Category.Object.Coproduct

-- A category has all binary coproducts
import Category.Object.Coproducts

-- An exponential object
import Category.Object.Exponential

-- An initial object
import Category.Object.Initial

-- The product of two objects
import Category.Object.Product

-- All binary products
import Category.Object.Products

-- Subobject classifiers (for topoi)
import Category.Object.SubobjectClassifier

-- Terminal object
import Category.Object.Terminal

-- Zero object (initial and terminal)
import Category.Object.Zero


-- A preorder gives rise to a category
import Category.Preorder

-- The product of two categories
import Category.Product

-- Pullbacks in a category
import Category.Pullback

-- Pushouts in a category
import Category.Pushout

-- All categories can have a slice category defined on them
import Category.Slice

-- The terminal category (a terminal object in the category of small categories)
import Category.Terminal

-- A topos
import Category.Topos