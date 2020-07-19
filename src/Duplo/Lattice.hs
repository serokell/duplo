
{- | Partial order, the `<=` operator of `Ord`. -}
module Duplo.Lattice where

{- | Ability to be partially ordered. -}
class Eq i => Lattice i where
  leq :: i -> i -> Bool

instance Lattice () where
  leq () () = True
