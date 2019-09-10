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
module Experiment where

import Language.Haskell.TH
import NP

countA :: A -> Int
countA = $$gcount

showA :: A -> String
showA = $$gshow

enumC :: [C]
enumC = $$cgenum

gettersR :: NP ((->) R) '[ A, B, C ]
gettersR = $$ggetters

settersR :: NP (Setter' R) '[ A, B, C ]
settersR = $$gsetters

compareA :: A -> A -> Ordering
compareA = $$gcompare

compareC :: C -> C -> Ordering
compareC = $$gcompare

--
-- dumb (MkA1 i c b) = sum [1, 1, 1]
-- dumb (MkA2 d)     = sum [1]

{-
dumb :: B -> [Int]
dumb b = $$(collapse_NP (map_NP (const (K [|| 1 ||])) (fromB [|| b ||])))

test :: [Int]
test = dumb (MkB 3 'x' True)
-}
