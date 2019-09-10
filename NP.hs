{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
{-# LANGUAGE UndecidableSuperClasses #-}
module NP where

import Data.Kind
import Data.Proxy
import GHC.Exts (build)
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Syntax hiding (Type)

type Code a = Q (TExp a)
type CodeF = Q :.: TExp

data NP (f :: k -> Type) :: [k] -> Type where
  Nil :: NP f '[]
  (:*) :: f x -> NP f xs -> NP f (x : xs)

infixr 5 :*

data NS (f :: k -> Type) :: [k] -> Type where
  Z :: f x -> NS f (x : xs)
  S :: NS f xs -> NS f (x : xs)

newtype (f :.: g) x = Comp { unComp :: f (g x) }

newtype SOP (f :: k -> Type) (xss :: [[k]]) = SOP (NS (NP f) xss)

np :: NP CodeF xs -> Code (NP I xs)
np Nil            = [|| Nil ||]
np (Comp c :* cs) = [|| I $$c :* $$(np cs) ||]

-- build :: (forall r . (a -> r -> r) -> r -> r) -> [a]

collapse_NP :: NP (K (Code a)) xs -> Code [a]
collapse_NP np =
  [|| build (\ cons nil -> $$(collapse_NP' [|| cons ||] [|| nil ||] np)) ||]

collapse_NP' :: Code (a -> r -> r) -> Code r -> NP (K (Code a)) xs -> Code r
collapse_NP' cons nil Nil         = nil
collapse_NP' cons nil (K a :* xs) = [|| $$cons $$a $$(collapse_NP' cons nil xs) ||]

ns :: NS (CodeF :.: f) xs -> Code (NS f xs)
ns (Z (Comp (Comp c))) = [|| Z $$c ||]
ns (S x)               = [|| S $$(ns x) ||]

collapse_NS :: NS (K (Code a)) xs -> Code a
collapse_NS (Z (K a)) = a
collapse_NS (S y)     = collapse_NS y

map_NP :: (forall x . f x -> g x) -> NP f xs -> NP g xs
map_NP f Nil       = Nil
map_NP f (x :* xs) = f x :* map_NP f xs

cmap_NP :: forall c f g xs . All c xs => (forall x . c x => f x -> g x) -> NP f xs -> NP g xs
cmap_NP f Nil       = Nil
cmap_NP f (x :* xs) = f x :* cmap_NP @c f xs

map_NS :: (forall x . f x -> g x) -> NS f xs -> NS g xs
map_NS f (Z x) = Z (f x)
map_NS f (S y) = S (map_NS f y)

cmap_NS :: forall c f g xs . All c xs => (forall x . c x => f x -> g x) -> NS f xs -> NS g xs
cmap_NS f (Z x) = Z (f x)
cmap_NS f (S y) = S (cmap_NS @c f y)

map_SOP :: (forall x . f x -> g x) -> SOP f xss -> SOP g xss
map_SOP f (SOP x) = SOP (map_NS (map_NP f) x)

cmap_SOP :: forall c f g xss . All (All c) xss => (forall x . c x => f x -> g x) -> SOP f xss -> SOP g xss
cmap_SOP f (SOP x) = SOP (cmap_NS @(All c) (cmap_NP @c f) x)

sop :: SOP CodeF xss -> Code (SOP I xss)
sop (SOP x) = [|| SOP $$(ns (map_NS (\ y -> Comp (Comp (np y))) x)) ||]

collapse_SOP :: SOP (K (Code a)) xss -> Code [a]
collapse_SOP (SOP x) = [|| $$(collapse_NS (map_NS (K . collapse_NP) x)) ||]

data A = MkA1 Int Char Bool | MkA2 Double

data B = MkB { getInt :: Int, getCh :: Char, getBool :: Bool }

{-
fromA :: A -> SOP I '[ '[Int, Char, Bool], '[Double] ]
fromA (MkA1 i c b) = SOP (Z (I i :* I c :* I b :* Nil))
fromA (MkA2 d)     = SOP (S (Z (I d :* Nil)))
-}

fromA1 :: Code Int -> Code Char -> Code Bool -> SOP CodeF '[ '[Int, Char, Bool], '[Double] ]
fromA1 i c b = SOP (Z (Comp i :* Comp c :* Comp b :* Nil))

fromA2 :: Code Double -> SOP CodeF '[ '[Int, Char, Bool], '[Double] ]
fromA2 d = SOP (S (Z (Comp d :* Nil)))

fromA :: Code A -> (SOP CodeF '[ '[Int, Char, Bool], '[Double] ] -> Code r) -> Code r
fromA a k =
  [|| case $$a of
        MkA1 i c b -> $$(k (fromA1 [|| i ||] [|| c ||] [|| b ||]))
        MkA2 d     -> $$(k (fromA2 [|| d ||]))
  ||]

class Generic a where
  type Description a :: [[Type]]
  from :: Code a -> (SOP CodeF (Description a) -> Code r) -> Code r

instance Generic A where
  type Description A = '[ '[Int, Char, Bool], '[Double] ]
  from = fromA

fromB :: Code B -> NP CodeF '[Int, Char, Bool]
fromB cb = Comp [|| getInt $$cb ||] :* Comp [|| getCh $$cb ||] :* Comp [|| getBool $$cb ||] :* Nil

data SList (xs :: [k]) :: Type where
  SNil  :: SList '[]
  SCons :: SListI xs => SList (x : xs)

class SListI (xs :: [k]) where
  sList :: SList xs

instance SListI '[] where
  sList = SNil

instance SListI xs => SListI (x : xs) where
  sList = SCons

class AllF c xs => All (c :: k -> Constraint) xs
instance AllF c xs => All c xs

type family AllF (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllF c '[] = ()
  AllF c (x : xs) = (c x, AllF c xs)

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

{-
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
-}

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

capply :: Code (a -> b) -> Code a -> Code b
capply cf cx = [|| $$cf $$cx ||]

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

gcount :: forall a . Generic a => Code (a -> Int)
gcount =
  [|| \ a -> $$(from [|| a ||] (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||])))) ||]

gshow :: forall a . (Generic a, All (All Show) (Description a)) => Code (a -> String)
gshow =
  [|| \ a -> $$(from [|| a ||] (capply [|| concat ||] . collapse_SOP . cmap_SOP @Show (\ (Comp x) -> K (capply [|| show ||] x)))) ||]
