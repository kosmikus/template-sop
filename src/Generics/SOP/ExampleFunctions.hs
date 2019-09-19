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
module Generics.SOP.ExampleFunctions where

import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Universe
import qualified GHC.Generics as GHC

import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.NS
import Generics.SOP.Universe
import qualified GHC.Generics as GHC
import Language.Haskell.TH

type Syntax a = Q (TExp a)
type SyntaxF = Q :.: TExp

syntactifyList :: [Syntax a] -> Syntax [a]
syntactifyList [] = [|| [] ||]
syntactifyList (x : xs) = [|| $$x : $$(syntactifyList xs) ||]

syntactifyNP :: NP (SyntaxF :.: f) xs -> Syntax (NP f xs)
syntactifyNP Nil = [|| Nil ||]
syntactifyNP (Comp (Comp x) :* xs) = [|| $$x :* $$(syntactifyNP xs) ||]

class Generic a => GenericSyntax a where
  sfrom :: Syntax a -> (SOP SyntaxF (Code a) -> Syntax r) -> Syntax r
  sto   :: SOP SyntaxF (Code a) -> Syntax a

sapply :: Syntax (a -> b) -> Syntax a -> Syntax b
sapply cf cx = [|| $$cf $$cx ||]


data BinTree a =
  Tip | Bin (BinTree a) a (BinTree a)
  deriving (GHC.Generic, Generic)

instance GenericSyntax (BinTree a) where
  sfrom treeSyntax k =
    [|| case $$treeSyntax of
          Tip       -> $$(k (SOP (Z Nil)))
          Bin l x r -> $$(k (SOP (S (Z (Comp [|| l ||] :* Comp [|| x ||] :* Comp [|| r ||] :* Nil)))))
    ||]

  sto (SOP (Z Nil)) = [|| Tip ||]
  sto (SOP (S (Z (Comp l :* Comp x :* Comp r :* Nil)))) = [|| Bin $$l $$x $$r ||]


gcompare :: (GenericSyntax a, All (All Ord) (Code a)) => Syntax (a -> a -> Ordering)
gcompare =
  [|| \ x y -> $$(sfrom [|| x ||] (\ x' -> sfrom [|| y ||] (\ y' -> go (unSOP x') (unSOP y')))) ||]
  where
    go :: forall xss . All (All Ord) xss => NS (NP SyntaxF) xss -> NS (NP SyntaxF) xss -> Syntax Ordering
    go (Z x) (Z y) =
      sapply [|| foldr (<>) EQ ||]
             (syntactifyList
             (collapse_NP
              (czipWith_NP (Proxy @Ord) (\ (Comp a) (Comp b) -> K [|| compare $$a $$b ||])
              x
              y)))
    go (Z _) (S _) = [|| LT ||]
    go (S _) (Z _) = [|| GT ||]
    go (S x) (S y) = go x y
