{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Instantiations where

import Data.Functor.Identity
import SOP
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Lib.Internal

sappend_Foo :: Foo -> Foo -> Foo
sappend_Foo foo1 foo2 = $$(sgsappend [|| foo1 ||] [|| foo2 ||])

sappend_Foo' :: Foo -> Foo -> Foo
sappend_Foo' = $$(sgsappend')

sappend_Pair :: (Semigroup a, Semigroup b) => Pair a b -> Pair a b -> Pair a b
sappend_Pair p1 p2 = $$(sgsappend [|| p1 ||] [|| p2 ||])

sappend_Pair' :: (Semigroup a, Semigroup b) => Pair a b -> Pair a b -> Pair a b
sappend_Pair' = $$(sgsappend')

instance NFData a => NFData (Tree a) where
  rnf t = $$(sgrnf [|| t ||])

eq_Ordering :: Ordering -> Ordering -> Bool
eq_Ordering o1 o2 = $$(sgeq [|| o1 ||] [|| o2 ||])

instance Eq a => Eq (Tree a) where
  (==) t1 t2 = $$(sgeq [|| t1 ||] [|| t2 ||])

showEnum_Ordering :: Ordering -> String
showEnum_Ordering o =
  $$(sgShowEnum (K "<" :* K "=" :* K ">=" :* Nil) [|| o ||])

-- fromRow_Person :: RowParser Person
-- fromRow_Person = $$(sgfromRow)

test :: Eq a => [a] -> [a] -> Bool
test = $$eqList
