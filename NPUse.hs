{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module NPUse where

import NP

testPureK :: NP (K Int) '[Int, Char, Bool]
testPureK = $$(pureK 3)

testPureNP :: NP Maybe '[Int, Char, Bool]
testPureNP = $$([|| $$(pure_NP) (Fun0 Nothing) ||])

testCPureNP :: NP I '[Int, Char, Bool]
testCPureNP = $$(cpure_NP @Default @'[Int, Char, Bool]) (CFun0 (I def))


bar :: NP [] '[Int, Char, Bool]
bar = $$(map_NP @'[Int, Char, Bool]) (Fun1 (\ (I x) -> [x])) (I 3 :* I 'z' :* I True :* Nil)
