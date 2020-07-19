
{- | Partial order, the `<=` operator of `Ord`. -}
module Duplo.Lattice where

{- | Ability to be partially ordered. -}
class Eq i => Lattice i where
  leq :: i -> i -> Bool

instance Lattice () where
  leq () () = True

partOrder :: Lattice l => l -> l -> Ordering
partOrder a b | leq a b && leq b a = EQ
partOrder a b | leq a b            = LT
partOrder a b |            leq b a = GT
partOrder _ _                      = error "partOrder: Non-orderable"
