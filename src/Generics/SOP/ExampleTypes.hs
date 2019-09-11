{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Generics.SOP.ExampleTypes where

import Generics.SOP
import Generics.SOP.Syntax
import qualified GHC.Generics as GHC

data ABC =
  A | B | C
  deriving (GHC.Generic, Generic, Show)

data Rec =
  MkRec { _rabc :: ABC, _rn :: Int, _rb :: Bool }
  deriving (GHC.Generic, Generic, Show)

data BinTree a =
  Tip | Bin (BinTree a) a (BinTree a)
  deriving (GHC.Generic, Generic)

instance GenericSyntax ABC where
  sfrom abcSyntax k =
    [|| case $$abcSyntax of
          A -> $$(k (SOP (Z Nil)))
          B -> $$(k (SOP (S (Z Nil))))
          C -> $$(k (SOP (S (S (Z Nil)))))
    ||]

  sto (SOP (Z Nil)) = [|| A ||]
  sto (SOP (S (Z Nil))) = [|| B ||]
  sto (SOP (S (S (Z Nil)))) = [|| C ||]

instance GenericSyntax Rec where
  sfrom recSyntax k =
    [|| case $$recSyntax of
          MkRec rabc rn rb ->
            $$(k (SOP (Z (Comp [|| rabc ||] :* Comp [|| rn ||] :* Comp [|| rb ||] :* Nil))))
    ||]

  sto (SOP (Z (Comp rabc :* Comp rn :* Comp rb :* Nil))) = [|| MkRec $$rabc $$rn $$rb ||]

instance GenericSyntax (BinTree a) where
  sfrom treeSyntax k =
    [|| case $$treeSyntax of
          Tip       -> $$(k (SOP (Z Nil)))
          Bin l x r -> $$(k (SOP (S (Z (Comp [|| l ||] :* Comp [|| x ||] :* Comp [|| r ||] :* Nil)))))
    ||]

  sto (SOP (Z Nil)) = [|| Tip ||]
  sto (SOP (S (Z (Comp l :* Comp x :* Comp r :* Nil)))) = [|| Bin $$l $$x $$r ||]

