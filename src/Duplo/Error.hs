
{- | The node for parse errors. -}
module Duplo.Error where

import Duplo.Pretty

{- | The container for a error. -}
data Err msg self
  = Err { errMsg :: msg }
  deriving stock (Functor, Foldable, Traversable)

instance Pretty msg => Pretty1 (Err msg) where
  pp1 (Err msg) = "▒" <.> pp msg <.> "▓"
