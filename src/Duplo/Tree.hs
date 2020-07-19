{-# OPTIONS_GHC -fno-warn-orphans #-}

{- | This module defines the structure and folds over the source tree skeleton.
-}

module Duplo.Tree
  ( -- * AST
    Tree
  , make
  , match
  , only
  , gist
  , layer

    -- * Constraints
  , Layers
  , Scoped (..)
  , usingScope

    -- * AST transformations
  , Ascent (..)
  , ascent
  , Descent (..)
  , descent
  , loop
  , loop'

    -- * Lookup
  , spineTo
  ) where

import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad

import Data.Foldable
import Data.Maybe
import Data.Sum

import Duplo.Lattice
import Duplo.Pretty

{- | The tree is an @info@ and one of @layers@ functors with subtrees in its values.

     (The @layers@ are the collection of possible nodes /in no particular order/.)
-}
type Tree layers = Cofree (Sum layers)

instance Apply Pretty1 layers => Pretty1 (Sum layers) where
  pp1 = apply @Pretty1 pp1

{- | The collection of typical needs -}
type Layers fs =
  ( Apply Functor fs
  , Apply Foldable fs
  , Apply Traversable fs
  , Apply Pretty1 fs
  )

instance (Layers layers, Modifies info) => Pretty (Tree layers info) where
  pp (d :< f) = ascribe d $ pp1 $ fmap pp f

{- | Ascending transformation from one `Tree` into another one.

     Converts both @info@ and @layers@.
-}
data Ascent fs gs a b m where
  {- | Wrap the node (the ascent is for), by forgetting its type. -}
  Ascent
    :: forall f g fs gs a b m
    .  ( Element f fs, Traversable f
       , Element g gs, Traversable g
       )
    => ((a, f (Tree gs b)) -> m (b, g (Tree gs b)))  -- ^ 1-layer transformation
    -> Ascent fs gs a b m

{- | Reconstruct the tree bottom-up. -}
ascent
  :: forall a b fs gs m
  .  (Monad m, Lattice b, Apply Functor gs)
  => (Tree fs a -> m (Tree gs b))  -- ^ The default handler.
  -> [Ascent fs gs a b m]          -- ^ The concrete handlers for chosen node types.
  -> Tree fs a                     -- ^ The tree to ascent.
  -> m (Tree gs b)
ascent fallback transforms = restart
  where
    restart = go transforms

    go (Ascent handler : rest) tree = do
      case match tree of
        Just (i, f) -> do
          f'        <- traverse restart f
          (i', f'') <- handler (i, f')
          return $ make (i', f'')

        Nothing -> do
          go rest tree

    go [] tree = fallback tree

{- | Descending transformation from one `Tree` into another one.

     Converts both @info@ and @layers@.
-}
data Descent fs gs a b m where
  {- | Wrap the node (the adecent is for), by forgetting its type. -}
  Descent
    :: forall f g fs gs a b m
    .  ( Element f fs, Traversable f
       , Element g gs, Traversable g
       )
    => ((a, f (Tree fs a)) -> m (b, g (Tree fs a)))  -- ^ 1-layer transformation
    -> Descent fs gs a b m

{- | Reconstruct the tree top-down. -}
descent
  :: forall a b fs gs m
  .  (Monad m, Lattice b, Apply Functor gs)
  => (Tree fs a -> m (Tree gs b))  -- ^ The default handler
  -> [Descent fs gs a b m]         -- ^ The concrete handlers for chosen nodes
  -> Tree fs a                     -- ^ The tree to ascent.
  -> m (Tree gs b)
descent fallback transforms = restart
  where
    restart = go transforms

    go (Descent handler : rest) tree = do
      case match tree of
        Just (i, f) -> do
          (i', f') <- handler (i, f)
          f''      <- traverse restart f'
          return $ make (i', f'')

        Nothing -> do
          go rest tree

    go [] tree = fallback tree

{- | Construct a tree out of annotation and a node (with subtrees). -}
make :: (Lattice i, Element f fs, Foldable f, Apply Functor fs) => (i, f (Tree fs i)) -> Tree fs i
make (i, f)
  | any (not . (`leq` i)) (extract <$> toList f) = error "Tree.make: Subtrees must be less of equal"
  | otherwise                                    = i :< inject f

{- | Attempt extraction of info and node from current root. -}
match :: Element f fs => Tree fs i -> Maybe (i, f (Tree fs i))
match (i :< f) = do
  f' <- project f
  return (i, f')

{- | Attempt extraction of node from current root. -}
layer :: Element f fs => Tree fs i -> Maybe (f (Tree fs i))
layer (_ :< f) = project f

{- | Attempt unsafe extraction of info and node from current root. -}
only :: Element f fs => Tree fs i -> (i, f (Tree fs i))
only (i :< f) = (i, fromJust $ project f)

{- | Attempt unsafe extraction of node from current root. -}
gist :: Element f fs => Tree fs i -> f (Tree fs i)
gist (_ :< f) = fromJust $ project f

{- | Apply a transform until it fails. -}
loop :: Monad m => (a -> m (Maybe a)) -> a -> m a
loop f = go
  where
    go a = f a >>= maybe (return a) go

{- | Apply a pure transform until it fails. -}
loop' :: Monad m => (a -> Maybe a) -> a -> m a
loop' f = return . go
  where
    go a = maybe a go $ f a

{- | Construct a sequence of trees, covering given point, bottom-up. -}
spineTo :: (Apply Foldable fs, Lattice i) => i -> Tree fs i -> [Tree fs i]
spineTo i = head . go []
  where
    go acc tree@(i' :< (toList -> trees)) = do
      unless (i `leq` i') do
        fail ""

      if null trees
      then do return acc
      else do go (tree : acc) =<< trees

{- | Ability to have some scoped calculations. -}
class Monad m => Scoped i m f where
  enter :: i -> f a -> m ()
  leave :: i -> f a -> m ()

{- | Convert a `Descent` into a `Scoped` Descent. -}
usingScope :: forall a b fs gs m. (Monad m, Apply (Scoped a m) fs) => Descent fs gs a b m -> Descent fs gs a b m
usingScope (Descent action) = Descent \(a, f) -> do
  -- So. To unpack `Apply X fs` constraint to get `X f`, ypu do `apply :: (forall g. c g => g a -> b) -> Sum fs a -> b`.
  -- The problem is, we have `f a`, not `Sum fs a`. Which I clutch up here by calling `inject @_ @fs f`.
  apply @(Scoped a m) (enter a) (inject @_ @fs f)
  res <- action (a, f)
  apply @(Scoped a m) (leave a) (inject @_ @fs f)
  return res
