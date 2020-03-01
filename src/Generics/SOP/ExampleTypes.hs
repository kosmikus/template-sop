{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
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
import Generics.SOP.Syntax.TH
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

data BinTree2 a =
  Tip2 | Bin2 (BinTree2 a) a (BinTree2 a)
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

{-

let x = $$(sfrom [|| Tip2 ||] (sto @(BinTree2 Int)))
<interactive>:16:12-51: Splicing expression
    sfrom [|| Tip2 ||] (sto @(BinTree2 Int))
  ======>
    case Tip2 of
      Tip2 -> Tip2
      Bin2 _x1_azd7 _x2_azd8 _x3_azd9
        -> ((Bin2 _x1_azd7) _x2_azd8) _x3_azd9

-}
deriveGenericSyntax ''BinTree2
