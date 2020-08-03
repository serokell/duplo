
{- | An extension of 'Text.PrettyPrint'.
-}

module Duplo.Pretty
  ( module Duplo.Pretty
  , module Text.PrettyPrint
  )
  where

import qualified Data.Text as Text
import Data.Text (Text, pack)

import Text.PrettyPrint hiding ((<>))

-- | Pretty-print to `Text`. Through `String`. Yep.
ppToText :: Pretty a => a -> Text
ppToText = pack . show . pp

{- | A typeclass for pretty-printable stuff.
-}
class Pretty p where
  pp :: p -> Doc

instance Pretty () where
  pp _ = "()"

instance Pretty1 Maybe where
  pp1 = maybe empty pp

instance {-# OVERLAPS #-} (Pretty a, Pretty b) => Pretty (Either a b) where
  pp = either pp pp

instance Pretty Int where
  pp = int

-- | Common instance.
instance Pretty Text where
  pp = text . Text.unpack

-- | Common instance.
instance Pretty Doc where
  pp = id
{- | A typeclass for pretty-printable functors.
-}
class Pretty1 p where
  pp1 :: p Doc -> Doc

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty1 p, Functor p) => Pretty (p a) where
  pp = pp1 . fmap pp

instance Pretty1 [] where
  pp1 = list

{- | A wrapper to make `Show` instances from `Pretty` ones.

     > data X a = X
     >   deriving Show via PP (X a)
-}
newtype PP a = PP { unPP :: a }

instance Pretty a => Show (PP a) where
  show = show . pp . unPP

{- | The class for annotations.
-}
class Modifies d where
  ascribe :: d -> Doc -> Doc

instance Modifies () where
  ascribe () = id

{- | The replacement for `Text.PrettyPrint.<>`.
-}
infixl 6 <.>
(<.>) :: Doc -> Doc -> Doc
(<.>) = (<>)

-- | Colorize a `Doc`.
color :: Int -> Doc -> Doc
color c d = zeroWidthText begin <.> d <.> zeroWidthText end
  where
    begin = "\x1b[" ++ show (30 + c) ++ "m"
    end   = "\x1b[0m"

-- | Decorate list of stuff as a tuple.
tuple :: Pretty p => [p] -> Doc
tuple = parens . train ","

-- | Decorate list of stuff as a list.
list :: Pretty p => [p] -> Doc
list = brackets . train ";"

infixr 2 `indent`
-- | First argument is a header to an indented second one.
indent :: Doc -> Doc -> Doc
indent a b = hang a 2 b

infixr 1 `above`
-- | Horisontal composition.
above :: Doc -> Doc -> Doc
above a b = hang a 0 b

-- | Pretty print as a sequence with given separator.
train :: Pretty p => Doc -> [p] -> Doc
train sep' = fsep . punctuate sep' . map pp

-- | Pretty print as a vertical block.
block :: Pretty p => [p] -> Doc
block = foldr ($+$) empty . map pp

-- | For pretty-printing qualified names.
sepByDot :: Pretty p => [p] -> Doc
sepByDot = cat . map (("." <.>) . pp)

-- | For pretty-printing `Maybe`s.
mb :: Pretty a => (Doc -> Doc) -> Maybe a -> Doc
mb f = maybe empty (f . pp)

-- | Pretty print as a vertical with elements separated by newline.
sparseBlock :: Pretty a => [a] -> Doc
sparseBlock = vcat . punctuate "\n" . map (($$ empty) . pp)

