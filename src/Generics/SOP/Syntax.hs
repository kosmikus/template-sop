{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
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

-- | Perform the 'sto' transformation in an applicative context.
stoA :: forall a f . (GenericSyntax a, Applicative f) => SOP (SyntaxF :.: f) (Code a) -> Syntax (f a)
stoA (SOP sop) =
  let
    go :: Syntax (f (Curry a xs)) -> NP (SyntaxF :.: f) xs -> Syntax (f a)
    go acc Nil                   = acc
    go acc (Comp (Comp x) :* xs) = go [|| $$acc <*> $$x ||] xs
  in
    collapse_NS $
      hczipWith (Proxy @SListI)
        (\ (Fn inj) -> K . go [|| pure $$(scurry_NP @a $ sto . SOP . unK . inj) ||])
        (injections @(Code a) @(NP SyntaxF))
        sop

type family Curry r xs where
  Curry r '[] = r
  Curry r (x : xs) = x -> Curry r xs

scurry_NP :: forall r xs . SListI xs => (NP SyntaxF xs -> Syntax r) -> Syntax (Curry r xs)
scurry_NP f =
  case sList :: SList xs of
    SNil  -> f Nil
    SCons -> [|| \ x -> $$(scurry_NP (\ xs -> f (Comp [|| x ||] :* xs))) ||]

{-

-- Only to demontrate how 'go' in 'stoA' is really an instance of 'foldl' on 'NP's.
-- It does not help clarity to do it in this way, though, because of the need for the 'newtype'.

foldl_NP :: (forall y ys . r (y : ys) -> f y -> r ys) -> r xs -> NP f xs -> r '[]
foldl_NP op acc Nil = acc
foldl_NP op acc (x :* xs) = foldl_NP op (op acc x) xs

newtype Helper f a xs = MkHelper { unHelper :: Syntax (f (Curry a xs)) }

go' :: Applicative f => Syntax (f (Curry a xs)) -> NP (SyntaxF :.: f) xs -> Syntax (f a)
go' acc np = unHelper (foldl_NP (\ (MkHelper acc') (Comp (Comp x)) -> MkHelper [|| $$acc' <*> $$x ||]) (MkHelper acc) np)
-}

sproductTypeFrom ::
  (IsProductType a xs, GenericSyntax a) =>
  Syntax a -> (NP SyntaxF xs -> Syntax r) -> Syntax r
sproductTypeFrom sa k = sfrom sa $ k . unZ . unSOP

sproductTypeTo :: (IsProductType a xs, GenericSyntax a) => NP SyntaxF xs -> Syntax a
sproductTypeTo np = sto (SOP (Z np))

sproductTypeToA :: (IsProductType a xs, GenericSyntax a, Applicative f) => NP (SyntaxF :.: f) xs -> Syntax (f a)
sproductTypeToA np = stoA (SOP (Z np))

senumTypeFrom :: (IsEnumType a, GenericSyntax a) => Syntax a -> (NS (K ()) (Code a) -> Syntax r) -> Syntax r
senumTypeFrom aSyntax k = sfrom aSyntax (k . map_NS (const (K ())) . unSOP)

senumTypeTo :: (IsEnumType a, GenericSyntax a) => NS (K ()) (Code a) -> Syntax a
senumTypeTo ns = sto (SOP (cmap_NS (Proxy @((~) '[])) (const Nil) ns))

senumTypeToA :: (IsEnumType a, GenericSyntax a, Applicative f) => NS (K ()) (Code a) -> Syntax (f a)
senumTypeToA ns = stoA (SOP (cmap_NS (Proxy @((~) '[])) (const Nil) ns))

sapply :: Syntax (a -> b) -> Syntax a -> Syntax b
sapply cf cx = [|| $$cf $$cx ||]

mapQQQ :: Syntax (a -> b -> c) -> SyntaxF a -> SyntaxF b -> SyntaxF c
mapQQQ f (Comp a) (Comp b) = Comp [|| $$f $$a $$b ||]
