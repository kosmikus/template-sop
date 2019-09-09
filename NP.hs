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
module NP where

import Data.Kind
import Data.Proxy
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Syntax hiding (Type)

type Code a = Q (TExp a)

data NP (f :: k -> Type) :: [k] -> Type where
  Nil :: NP f '[]
  (:*) :: f x -> NP f xs -> NP f (x : xs)

infixr 5 :*

data SList (xs :: [k]) :: Type where
  SNil  :: SList '[]
  SCons :: SListI xs => SList (x : xs)

class SListI (xs :: [k]) where
  sList :: SList xs

instance SListI '[] where
  sList = SNil

instance SListI xs => SListI (x : xs) where
  sList = SCons

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[] = ()
  All c (x : xs) = (c x, All c xs)

newtype K a b = K a
newtype I a   = I a

pureK :: forall xs a . (Lift a, SListI xs) => a -> Code (NP (K a) xs)
pureK p =
  case sList @_ @xs of
    SNil  -> [|| Nil ||]
    SCons -> [|| K p :* $$(pureK p) ||]

newtype  Fun0   f   = Fun0  { unFun0  :: forall x . f x }
newtype  Fun1   f g = Fun1  { unFun1  :: forall x . f x -> g x }
newtype CFun0 c f   = CFun0 { unCFun0 :: forall x . c x => f x }

pure_NP :: forall xs f . (SListI xs) => Code (Fun0 f -> (NP f xs))
pure_NP =
  case sList @_ @xs of
    SNil  -> [|| \ p -> Nil ||]
    SCons -> [|| \ p -> unFun0 p :* $$pure_NP p ||]

cpure_NP :: forall c xs f . (All c xs, SListI xs) => Code (CFun0 c f -> NP f xs)
cpure_NP =
  case sList @_ @xs of
    SNil  -> [|| \ p -> Nil ||]
    SCons -> [|| \ p -> unCFun0 p :* $$cpure_NP p ||]

map_NP :: forall xs f g . (SListI xs) => Code (Fun1 f g -> NP f xs -> NP g xs)
map_NP =
  [|| \ f ->
    $$(case sList @_ @xs of
         SNil  -> [|| \ Nil -> Nil ||]
         SCons ->
           let
             r :: forall x xs' . SListI xs' => Code (NP f (x : xs') -> NP g (x : xs'))
             r = [|| \ (x :* (xs :: NP f xs')) -> unFun1 f x :* $$map_NP f xs ||]
           in
             r
      )
  ||]

tlProxy :: Proxy (x : xs) -> Proxy xs
tlProxy Proxy = Proxy

{-
map_NP :: forall xs f g . (SListI xs) => Q (TExp (Fun1 f g)) -> NP f xs -> Q (TExp (NP g xs))
map_NP fun np =
  case sList @_ @xs of
    SNil  -> case np of Nil -> [|| Nil ||]
    SCons ->
      case np of
        (x :* xs) ->
          let
            y = [|| $$(transform2 fun) ||]
          in
            _  -- [|| $$(transform2 fun [|| x ||]) :* $$(map_NP fun xs) ||]
-}

transform1 :: Code (a -> b) -> Code a -> Code b
transform1 cf cx = [|| $$cf $$cx ||]

transform2 :: Code (Fun1 f g) -> Code (f x) -> Code (g x)
transform2 cf cx = [|| unFun1 $$cf $$cx ||]

class Default a where
  def :: a

instance Default Int where
  def = 42

instance Default Char where
  def = 'x'

instance Default Bool where
  def = False

