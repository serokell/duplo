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
  , usingScope'
  , skip

    -- * AST transformations
  -- , Ascent (..)
  -- , ascent
  , Descent (..)
  , HandlerFailed (..)
  , descent
  , changeInfo
  , leaveBe
  , loop
  , loop'
  , Ascent' (..)
  , ascent'

    -- * AST Folding
  , Visit (..)
  , visit
  , collect

    -- * Lookup
  , spineTo

    -- * Re-export
  , module Data.Sum
  , module Control.Comonad
  , module Control.Comonad.Cofree
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad
import Control.Monad.Catch

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
    => DescentHandler f g a b fs m  -- ^ 1-layer transformation
    -> Descent fs gs a b m

type DescentHandler f g a b fs m = (a, f (Tree fs a)) -> m (b, g (Tree fs a))
type DescentDefault fs gs a b m
  =  (Tree fs a -> m (Tree gs b))
  ->  Tree fs a -> m (Tree gs b)

data HandlerFailed = HandlerFailed
  deriving stock Show
  deriving anyclass Exception

{- | Reconstruct the tree top-down. -}
descent
  :: forall a b fs gs m
  .  (MonadCatch m, Lattice b, Apply Functor gs, Apply Foldable gs, Apply Traversable gs)
  => DescentDefault fs gs a b m    -- ^ The default handler
  -> [Descent fs gs a b m]         -- ^ The concrete handlers for chosen nodes
  -> Tree fs a                     -- ^ The tree to ascent.
  -> m (Tree gs b)
descent fallback transforms = restart
  where
    restart :: Tree fs a -> m (Tree gs b)
    restart = go transforms

    go :: [Descent fs gs a b m] -> Tree fs a -> m (Tree gs b)
    go (Descent handler : rest) tree = do
        (i,  f)  <- matchOrFail tree
        (i', f') <- handler (i, f)
        f''      <- traverse restart f'
        return $ make (i', f'')
      `catch` \HandlerFailed -> do
        go rest tree

    go [] tree = do
      fallback restart tree
{-# INLINE descent #-}

data Ascent' fs gs a b where
  {- | Wrap the node (the adecent is for), by forgetting its type. -}
  Ascent'
    :: forall f g fs gs a b
    .  ( Element f fs, Traversable f
       , Element g gs, Traversable g
       )
    => AscentHandler' f gs a b  -- ^ 1-layer transformation
    -> Ascent' fs gs a b

type AscentHandler' f  gs a b  = (a,     f  (Tree gs b)) -> Tree gs b
type AscentDefault' fs gs a b  = (a, Sum fs (Tree gs b)) -> Tree gs b

{- | Reconstruct the tree top-down. -}
ascent'
  :: forall a b fs gs
  .  (Lattice b, Apply Functor fs)
  => AscentDefault' fs gs a b    -- ^ The default handler
  -> [Ascent' fs gs a b]         -- ^ The concrete handlers for chosen nodes
  -> Tree fs a                   -- ^ The tree to ascent.
  -> Tree gs b
ascent' fallback transforms = restart
  where
    restart :: Tree fs a -> Tree gs b
    restart (r :< f) = fromJust $ go transforms (r, fmap restart f)

    go :: [Ascent' fs gs a b] -> (a, Sum fs (Tree gs b)) -> Maybe (Tree gs b)
    go (Ascent' handler : rest) (i, f) = do
        f' <- project f
        return $ handler (i, f')
      <|>
        go rest (i, f)

    go [] (r, tree) = do
      return $ fallback (r, tree)

{-# INLINE ascent' #-}

data Visit fs a m where
  {- | Wrap the node (the adecent is for), by forgetting its type. -}
  Visit
    :: forall f fs a m
    .  ( Element f fs, Foldable f
       )
    => VisitHandler f a fs m  -- ^ 1-layer transformation
    -> Visit fs a m

type VisitHandler f a fs m = (a, f (Tree fs a)) -> m ()

visit
  :: forall a fs m
  .  (MonadCatch m, Apply Foldable fs)
  => [Visit fs a m]         -- ^ The concrete handlers for chosen nodes
  -> Tree fs a                     -- ^ The tree to ascent.
  -> m ()
visit visitors = restart
  where
    restart = go visitors

    go (Visit handler : rest) tree = do
        (a, f) <- matchOrFail tree
        handler (a, f)
        for_ f restart
      `catch` \HandlerFailed -> do
        go rest tree
    go [] (_ :< f) = do
      for_ f restart

{- | Construct a tree out of annotation and a node (with subtrees). -}
make :: (Lattice i, Element f fs, Foldable f, Apply Functor fs) => (i, f (Tree fs i)) -> Tree fs i
make (i, f)
  | any (not . (`leq` i)) (extract <$> toList f) = error "Tree.make: Subtrees must be less of equal"
  | otherwise                                    = i :< inject f
{-# INLINE make #-}

{- | Attempt extraction of info and node from current root. -}
match :: Element f fs => Tree fs i -> Maybe (i, f (Tree fs i))
match (i :< f) = do
  f' <- project f
  return (i, f')
{-# INLINE match #-}

matchOrFail :: (Element f fs, MonadThrow m) => Tree fs i -> m (i, f (Tree fs i))
matchOrFail = maybe (throwM HandlerFailed) return . match
{-# INLINE matchOrFail #-}

{- | Attempt extraction of node from current root. -}
layer :: Element f fs => Tree fs i -> Maybe (f (Tree fs i))
layer (_ :< f) = project f

{- | Attempt unsafe extraction of info and node from current root. -}
only :: Tree '[f] i -> (i, f (Tree '[f] i))
only (i :< f) = (i, fromJust $ project f)

{- | Attempt unsafe extraction of node from current root. -}
gist :: Element f fs => Tree fs i -> f (Tree fs i)
gist (_ :< f) = fromJust $ project f

{- | Apply a transform until it fails. -}
loop :: Monad m => (a -> m (Maybe a)) -> a -> m (Maybe a)
loop f = go
  where
    go a = f a >>= maybe (return $ Just a) go

{- | Apply a pure transform until it fails. -}
loop' :: Monad m => (a -> Maybe a) -> a -> m (Maybe a)
loop' f = return . go
  where
    go a = maybe (Just a) go $ f a

{- | Construct a sequence of trees, covering given point, bottom-up. -}
spineTo :: (Apply Foldable fs, Lattice i) => (i -> Bool) -> Tree fs i -> [Tree fs i]
spineTo covers tree =
  case go [] tree of
    x : _ -> x
    []    -> []
  where
    go acc tree'@(i' :< (toList -> trees)) = do
      unless (covers i') do
        fail ""

      if null trees
      then do return (tree' : acc)
      else do go     (tree' : acc) =<< trees

{- | Ability to have some scoped calculations. -}
class Monad m => Scoped i m a f where
  before :: i -> f a -> m ()
  after :: i -> f a -> m ()

  before _ _ = skip
  after _ _ = skip

{- | Default implementation for `enter`/`leave`. -}
skip :: Monad m => m ()
skip = return ()

{- | Convert a `Descent` into a `Scoped` Descent. -}
usingScope
  :: forall a b fs gs m
  .  ( Monad m
     , Apply (Scoped a m (Tree fs a)) fs
     )
  => Descent fs gs a b m
  -> Descent fs gs a b m
usingScope (Descent action) = Descent $ \(a, f) -> do
  -- So. To unpack `Apply X fs` constraint to get `X f`, ypu do `apply :: (forall g. c g => g a -> b) -> Sum fs a -> b`.
  -- The problem is, we have `f a`, not `Sum fs a`. Which I clutch up here by calling `inject @_ @fs f`.
  apply @(Scoped a m (Tree fs a)) (before a) (inject @_ @fs f)
  res <- action (a, f)
  apply @(Scoped a m (Tree fs a)) (after a) (inject @_ @fs f)
  return res
{-# INLINE usingScope #-}

{- | Convert a `Descent` into a `Scoped` Descent. -}
usingScope'
  :: forall a b fs gs m
  .  ( Monad m
     , Apply (Scoped a m (Tree fs a)) fs
     )
  => DescentDefault fs gs a b m
  -> DescentDefault fs gs a b m
usingScope' action restart tree@(a :< f) = do
  -- So. To unpack `Apply X fs` constraint to get `X f`, ypu do `apply :: (forall g. c g => g a -> b) -> Sum fs a -> b`.
  -- The problem is, we have `f a`, not `Sum fs a`. Which I clutch up here by calling `inject @_ @fs f`.
  apply @(Scoped a m (Tree fs a)) (before a) f
  res <- action restart tree
  apply @(Scoped a m (Tree fs a)) (after a) f
  return res
{-# INLINE usingScope' #-}

leaveBe
  :: ( Monad m
     , Apply Foldable fs
     , Apply Functor fs
     , Apply Traversable fs
     )
  => DescentDefault fs fs a a m
leaveBe restart (a :< f) = do
  f' <- traverse restart f
  return (a :< f')
{-# INLINE leaveBe #-}

changeInfo
  :: ( Monad m
     , Apply Foldable fs
     , Apply Functor fs
     , Apply Traversable fs
     )
  => (a -> b)
  -> DescentDefault fs fs a b m
changeInfo mapper restart (a :< f) = do
  f' <- traverse restart f
  return (mapper a :< f')
{-# INLINE changeInfo #-}

collect :: (Element f fs, Apply Foldable fs) => Tree fs a -> [(a, f (Tree fs a))]
collect tree@(_ :< f) =
  foldMap collect f <>
    case match tree of
      Just it -> [it]
      Nothing -> []
