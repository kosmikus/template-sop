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
import Generics.SOP.Syntax
import Generics.SOP.Universe
import qualified GHC.Generics as GHC

-- | Classic generic enum.
genum :: (IsEnumType a) => [a]
genum = enumTypeTo <$> apInjs_NP (pure_NP (K ()))

-- | Specialised generic enum.
sgenum :: (IsEnumType a, GenericSyntax a) => Syntax [a]
sgenum = syntactifyList (senumTypeTo <$> apInjs_NP (pure_NP (K ())))

newtype Setter s a = Setter (a -> s -> s)

-- | Classic generic setters.
gsetters :: (IsProductType s xs) => NP (Setter s) xs
gsetters =
  map_NP
    (\ (Setter' f) ->
      Setter (\ a s ->
        productTypeTo (f (I a) (productTypeFrom s))))
    npSetters

-- | Syntactic generic setters.
sgsetters :: (IsProductType s xs, GenericSyntax s) => Syntax (NP (Setter s) xs)
sgsetters =
  syntactifyNP (map_NP
    (\ (Setter' f) ->
      Comp (Comp
        [|| Setter (\ a s ->
              $$(sproductTypeFrom [|| s ||]
                  (\ s' -> sproductTypeTo (f (Comp [|| a ||]) s'))))
        ||]))
    npSetters)

npSetters :: forall xs f . (SListI xs) => NP (Setter' f xs) xs
npSetters = case sList @xs of
  SNil  -> Nil
  SCons -> Setter' (\ x (_ :* xs) -> x :* xs) :* map_NP shiftSetter npSetters

newtype Setter' f xs a = Setter' (f a -> NP f xs -> NP f xs)

shiftSetter :: Setter' f xs a -> Setter' f (x : xs) a
shiftSetter (Setter' f) = Setter' (\ y (x :* xs) -> x :* f y xs)

