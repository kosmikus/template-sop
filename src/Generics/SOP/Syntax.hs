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
module Generics.SOP.Syntax where

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
  sto'   :: SOP (SyntaxF :.: SyntaxF) (Code a) -> Syntax (Syntax a)



sproductTypeFrom ::
  (IsProductType a xs, GenericSyntax a) =>
  Syntax a -> (NP SyntaxF xs -> Syntax r) -> Syntax r
sproductTypeFrom sa k = sfrom sa $ k . unZ . unSOP

sproductTypeTo :: (IsProductType a xs, GenericSyntax a) => NP SyntaxF xs -> Syntax a
sproductTypeTo np = sto (SOP (Z np))

senumTypeFrom :: (IsEnumType a, GenericSyntax a) => Syntax a -> (NS (K ()) (Code a) -> Syntax r) -> Syntax r
senumTypeFrom aSyntax k = sfrom aSyntax (k . map_NS (const (K ())) . unSOP)

senumTypeTo :: (IsEnumType a, GenericSyntax a) => NS (K ()) (Code a) -> Syntax a
senumTypeTo ns = sto (SOP (cmap_NS (Proxy @((~) '[])) (const Nil) ns))

sapply :: Syntax (a -> b) -> Syntax a -> Syntax b
sapply cf cx = [|| $$cf $$cx ||]


