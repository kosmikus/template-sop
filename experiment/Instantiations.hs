{-# LANGUAGE TemplateHaskell #-}
module Instantiations where

import SOP
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Lib.Internal

sappend_Foo :: Foo -> Foo -> Foo
sappend_Foo foo1 foo2 = $$(sgsappend [|| foo1 ||] [|| foo2 ||])

sappend_Pair :: (Semigroup a, Semigroup b) => Pair a b -> Pair a b -> Pair a b
sappend_Pair p1 p2 = $$(sgsappend [|| p1 ||] [|| p2 ||])

