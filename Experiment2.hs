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
module Experiment2 where

import NP
import Experiment

gcount2 :: A -> Int
gcount2 a = $$( gfrom [|| a ||] (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||]))))


--  [|| \ a -> $$(from [|| a ||] (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||])))) ||]
