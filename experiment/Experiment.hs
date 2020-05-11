{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import NPMIN ()
import NP
import NPCompare


countA :: A -> Int
countA = $$gcount

showA :: A -> String
showA = $$gshow

--main = putStrLn (showA (MkA1 0 'a' True))

main = print $ compareA (MkA1 0 'a' True) (MkA2 0)

enumC :: [C]
enumC = $$cgenum

{-# INLINE compareA #-}
compareA :: A -> A -> Ordering
compareA = $$gcompare

compareC :: C -> C -> Ordering
compareC = $$gcompare

gettersR :: NPG ((->) R) '[ A, B, C ]
gettersR = $$ggetters

settersR :: NPG (Setter' R) '[ A, B, C ]
settersR = $$gsetters

{-

gfrom :: Code A -> (SOP CodeF (Description A) -> Code r) -> Code r
gfrom c k = unsafeTExpCoerce $ $(genFrom @A) (unTypeQ c) (unTypeQ . k)

caseA :: NP ((NP I -.-> K r)) (Description A) -> A -> r
caseA table = $$(unspillNP [|| table ||] gcase)
-}
-- caseA (f1 :* f2 :* Nil) a =
--   case a of
--     MkA1 i c b -> f1 i c b
--     MkA2 d     -> f2 d
--
-- caseA np a =
--   case a of
--     MkA1 i c b -> selZ np i c b
--     MkA2 d     -> selSZ d

--
-- dumb (MkA1 i c b) = sum [1, 1, 1]
-- dumb (MkA2 d)     = sum [1]

{-
dumb :: B -> [Int]
dumb b = $$(collapse_NP (map_NP (const (K [|| 1 ||])) (fromB [|| b ||])))

test :: [Int]
test = dumb (MkB 3 'x' True)
-}
