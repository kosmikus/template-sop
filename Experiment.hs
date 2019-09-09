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

import NP

dumb :: A -> Int
dumb a = $$(fromA [|| a ||] (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||]))))
--
-- dumb (MkA1 i c b) = sum [1, 1, 1]
-- dumb (MkA2 d)     = sum [1]

{-
dumb :: B -> [Int]
dumb b = $$(collapse_NP (map_NP (const (K [|| 1 ||])) (fromB [|| b ||])))

test :: [Int]
test = dumb (MkB 3 'x' True)
-}
