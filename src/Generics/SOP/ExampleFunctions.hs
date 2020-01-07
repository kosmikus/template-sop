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

import Control.DeepSeq

import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.NS
import Generics.SOP.Syntax
import Generics.SOP.Universe
import qualified GHC.Generics as GHC
import Language.Haskell.TH.Syntax

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

geq :: (GenericSyntax a, All (All Eq) (Code a)) => Syntax (a -> a -> Bool)
geq =
  [|| \ x y -> $$(sfrom [|| x ||] (\ x' -> sfrom [|| y ||] (\ y' ->
    ccompare_SOP
      (Proxy @Eq)
      [|| False ||]
      (\ a b -> (sapply [|| and ||] . syntactifyList . collapse_NP) (czipWith_NP (Proxy @Eq) (\ (Comp c) (Comp d) -> K [|| $$c == $$d ||]) a b))
      [|| False ||]
      x' y'
    )))
  ||]

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

grnf :: (GenericSyntax a, All (All NFData) (Code a)) => Syntax (a -> ())
grnf =
  [|| \ x -> $$(sfrom [|| x ||] $ \ x' ->
    sapply [|| rnf ||] (syntactifyList (collapse_SOP (cmap_SOP (Proxy @NFData) (K . sapply [|| rnf ||] . unComp) x')))
    )
  ||]

-- Need 8.10 for this unit of a function to be in the Lift class
liftTyped :: Lift a => a -> Q (TExp a)
liftTyped = unsafeTExpCoerce . lift

glift :: (Generic a, GenericSyntax a, All (All Lift) (Code a)) => a -> Syntax a
glift x = sto (cmap_SOP (Proxy @Lift) (\(I a) -> Comp (liftTyped a)) (from x))
