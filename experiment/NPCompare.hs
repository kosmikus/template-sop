{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
module NPCompare where

import NP
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Syntax hiding (Type)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Lib.Internal



gcompare :: ( (All (All (And LiftT (Compose CodeC Ord))) (Description a)), Generic a, All (All Ord) (Description a)) => Code (a -> a -> Ordering)
gcompare =
  [|| \ x y -> $$(from [|| x ||] (\ x' -> from [|| y ||] (\ y' -> go (unSOP x') (unSOP y')))) ||]
  where
    go :: forall xss . (All (All (And LiftT (Compose CodeC Ord))) xss) =>
            NS (NP CodeF) xss -> NS (NP CodeF) xss -> Code Ordering
    go (Z x) (Z y) = capply [|| foldr (<>) EQ ||] (collapse_NP (czipWith_NP @(And LiftT (Compose CodeC Ord)) (\ (Comp a) (Comp b) -> K [|| compare $$a $$b ||]) x y))
    go (Z _) (S _) = [|| LT ||]
    go (S _) (Z _) = [|| GT ||]
    go (S x) (S y) = go x y
