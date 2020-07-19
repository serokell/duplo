
module Duplo.Example where

import Duplo

data Expr self
  = App  self    self
  | Lam [String] self
  | Var  String
  deriving stock (Functor, Foldable, Traversable)

instance Pretty1 Expr where
  pp1 = \case
    App f  x -> parens (f <+> x)
    Lam ns x -> parens ("\\" <.> text (unwords ns) <+> "->" <+> x)
    Var n    -> text n

type AST = Tree '[Expr] ()

-- Substution-style greedy evaluator of lambda-calculus via recursive ascent.
evalStrict :: forall m. Monad m => AST -> m AST
evalStrict =
  ascent return
    [
      Ascent $ loop' \case
          -- if encounter "(\x ARGS -> EXPR1) EXPR2", call the former with the latter as argument
          -- "(\x ARGS -> EXPR1) EXPR2" ==> "(ARGS -> EXPR1 with x replaced by EXPR2)"
          (i, App (gist -> Lam (a : as) b) x) -> Just (i, Lam as $ subst a x b)

          -- Lambda with no arguments is its body.
          (_, Lam [] b)                       -> match b

          -- Everything else cannot be evaluated.
          _                                   -> Nothing
    ]
  where
    -- Substute a variable with a program.
    subst a (only -> ex) = go
      where
        go (only -> expr) = make $ case expr of
          (i, App f  x)             -> (i, App (go f) (go x))  -- substution of f(x) is recursion
          (_, Lam as _) | elem a as -> expr                    -- if lambda hides the name, stop
          (i, Lam as x)             -> (i, Lam as $ go x)      -- otherwise, recure
          (_, Var n)    | n == a    -> ex                      -- found a reference, replace
          (_, Var _)                -> expr                    -- wrong variable, leave it be

mk :: Expr AST -> AST
mk f = make ((), f)

test :: AST
test = mk (App (mk (Lam ["x"] $ mk (Lam ["y"] $ mk (Var "x")))) (mk (Var "a")))

runTest :: Monad m => m Doc
runTest = pp <$> evalStrict test