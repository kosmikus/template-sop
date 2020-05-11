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
{-# LANGUAGE ViewPatterns #-}
module SOP where

import Data.Kind
import Data.Proxy
import GHC.Exts (build)
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Syntax hiding (Type)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Lib.Internal
import Unsafe.Coerce

type Code a = Q (TExp a)
newtype C a = C (Code a)

data Dict (c :: k -> Constraint) (a :: k) where
  Dict :: c a => Dict c a

withDict :: Dict c a -> (c a => r) -> r
withDict Dict x = x

all_NP :: NP (Dict c) xs -> Dict (All c) xs
all_NP Nil          = Dict
all_NP (Dict :* ds) = withDict (all_NP ds) Dict

unAll_NP :: Dict (All c) xs -> NP (Dict c) xs
unAll_NP d = withDict d dicts_NP

dictImplies :: (SListI xs, forall x . c x => d x) => Dict (All c) xs -> Dict (All d) xs
dictImplies =
  dictImplies' (\ Dict -> Dict)

dictImplies' :: SListI xs => (forall x . Dict c x -> Dict d x) -> Dict (All c) xs -> Dict (All d) xs
dictImplies' f dict =
  all_NP (map_NP f (unAll_NP dict))

data NP (f :: k -> Type) :: [k] -> Type where
  Nil :: NP f '[]
  (:*) :: f x -> NP f xs -> NP f (x : xs)

infixr 5 :*

data NS (f :: k -> Type) :: [k] -> Type where
  Z :: f x -> NS f (x : xs)
  S :: NS f xs -> NS f (x : xs)

newtype (f :.: g) x = Comp { unComp :: f (g x) }

class (f (g x)) => (f `Compose` g) x
instance (f (g x)) => (f `Compose` g) x
infixr 9 `Compose`

class (f x, g x) => (f `And` g) x
instance (f x, g x) => (f `And` g) x
infixl 7 `And`

class Top x
instance Top x

newtype SOP (f :: k -> Type) (xss :: [[k]]) = SOP { unSOP :: NS (NP f) xss }
newtype POP (f :: k -> Type) (xss :: [[k]]) = POP { unPOP :: NP (NP f) xss }

type SListI = All LiftT

data SList :: [k] -> Type where
  SNil  :: SList '[]
  SCons :: SListI xs => SList (x ': xs)

class (AllF c xs) => All (c :: k -> Constraint) xs where
  cpara_SList ::
       proxy c
    -> r '[]
    -> (forall y ys . (c y, All c ys) => r ys -> r (y ': ys))
    -> r xs
  dicts_NP :: NP (Dict c) xs
  cpure_NP' :: (forall x . c x => f x) -> NP f xs

instance All c '[] where
  cpara_SList _p nil _cons = nil
  dicts_NP = Nil
  cpure_NP' p = Nil

instance (c x, All c xs) => All c (x : xs) where
  cpara_SList p nil cons =
    cons (cpara_SList p nil cons)
  dicts_NP = Dict :* dicts_NP
  cpure_NP' p = p :* cpure_NP' @_ @c p

ccase_SList ::
     All c xs
  => proxy c
  -> r '[]
  -> (forall y ys . (c y, All c ys) => r (y ': ys))
  -> r xs
ccase_SList p nil cons =
  cpara_SList p nil (const cons)

sList :: forall k (xs :: [k]) . SListI xs => SList xs
sList = ccase_SList (Proxy @LiftT) SNil SCons

type family AllF (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllF c '[] = ()
  AllF c (x : xs) = (c x, All c xs)

newtype K a b = K { unK :: a }
newtype I a   = I { unI :: a }

cmap_NP :: forall c f g xs . All c xs => (forall x . c x => f x -> g x) -> NP f xs -> NP g xs
cmap_NP f Nil       = Nil
cmap_NP f (x :* xs) = f x :* cmap_NP @c f xs

map_NP :: forall f g xs . SListI xs => (forall x . LiftT x => f x -> g x) -> NP f xs -> NP g xs
map_NP = cmap_NP @LiftT

cmap_NS :: forall c f g xs . All c xs => (forall x . c x => f x -> g x) -> NS f xs -> NS g xs
cmap_NS f (Z x) = Z (f x)
cmap_NS f (S y) = S (cmap_NS @c f y)

map_NS :: forall f g xs . SListI xs => (forall x . LiftT x => f x -> g x) -> NS f xs -> NS g xs
map_NS = cmap_NS @LiftT

cmap_SOP :: forall c f g xss . All (All c) xss => (forall x . c x => f x -> g x) -> SOP f xss -> SOP g xss
cmap_SOP f (SOP sop) = SOP (cmap_NS @(All c) (cmap_NP @c f) sop)

czipWith_NP :: forall c f g h xs . All c xs => (forall x . c x => f x -> g x -> h x) -> NP f xs -> NP g xs -> NP h xs
czipWith_NP f xs ys = cpure_NP @c (Fn $ \x -> Fn $ \ y -> f x y) `hap_NP` xs `hap_NP` ys

cselectWith_NS :: forall c f g h xs . All c xs => (forall x . c x => f x -> g x -> h x) -> NP f xs -> NS g xs -> NS h xs
cselectWith_NS f (x :* _)  (Z y) = Z (f x y)
cselectWith_NS f (_ :* xs) (S i) = S (cselectWith_NS @c f xs i)

selectWith_NS :: forall f g h xs . SListI xs => (forall x . LiftT x => f x -> g x -> h x) -> NP f xs -> NS g xs -> NS h xs
selectWith_NS = cselectWith_NS @LiftT

newtype (f -.-> g) x = Fn { apFn :: f x -> g x }

hap_NP :: NP (f -.-> g) xs -> NP f xs -> NP g xs
hap_NP Nil       Nil       = Nil
hap_NP (f :* fs) (x :* xs) = apFn f x :* hap_NP fs xs

cpure_NP :: forall c f xs . All c xs => (forall x . c x => f x) -> NP f xs
cpure_NP p = cpure_NP' @_ @c p

pure_NP :: forall f xs . SListI xs => (forall x . LiftT x => f x) -> NP f xs
pure_NP p = cpure_NP @LiftT p

collapse_NP :: NP (K a) xs -> [a]
collapse_NP Nil         = []
collapse_NP (K a :* xs) = a : collapse_NP xs

collapse_NS :: NS (K a) xs -> a
collapse_NS (Z (K x)) = x
collapse_NS (S i)     = collapse_NS i

collapse_SOP :: SOP (K a) xs -> [a]
collapse_SOP (SOP (Z xs)) = collapse_NP xs
collapse_SOP (SOP (S i))  = collapse_SOP (SOP i)

ccompare_NS ::
     forall c proxy r f g xs .
     (All c xs)
  => r                                    -- ^ what to do if first is smaller
  -> (forall x . c x => f x -> g x -> r)  -- ^ what to do if both are equal
  -> r                                    -- ^ what to do if first is larger
  -> NS f xs -> NS g xs
  -> r
ccompare_NS lt eq gt = go
  where
    go :: forall ys . (All c ys) => NS f ys -> NS g ys -> r
    go (Z x)  (Z y)  = eq x y
    go (Z _)  (S _)  = lt
    go (S _)  (Z _)  = gt
    go (S xs) (S ys) = go xs ys

ccompare_SOP ::
     forall c proxy r f g xss .
     (All (All c) xss)
  => r                                                  -- ^ what to do if first is smaller
  -> (forall xs . All c xs => NP f xs -> NP g xs -> r)  -- ^ what to do if both are equal
  -> r                                                  -- ^ what to do if first is larger
  -> SOP f xss -> SOP g xss
  -> r
ccompare_SOP lt eq gt (SOP xs) (SOP ys) =
  ccompare_NS @(All c) lt eq gt xs ys

class (LiftT a, SListI (Description a), All SListI (Description a)) => Generic a where
  type Description a :: [[Type]]
  -- ofrom :: a -> SOP I (Description a)
  from :: LiftT r => Code a -> (SOP C (Description a) -> Code r) -> Code r
  -- oto :: SOP I (Description a) -> a
  to :: SOP C (Description a) -> Code a

type IsProductType a xs = (Generic a, Description a ~ '[ xs ])
type IsEnumType a = (Generic a, All ((~) '[]) (Description a))

productTypeFrom :: (IsProductType a xs, LiftT r) => Code a -> (NP C xs -> Code r) -> Code r
productTypeFrom c k =
  from c $ \ (SOP (Z xs)) -> k xs

productTypeTo :: IsProductType a xs => NP C xs -> Code a
productTypeTo xs =
  to (SOP (Z xs))

enumTypeFrom :: (IsEnumType a, LiftT r) => Code a -> (NS (K ()) (Description a) -> Code r) -> Code r
enumTypeFrom c k =
  from c $ \ (SOP ns) -> k (cmap_NS @LiftT (const (K ())) ns)

class (CodeC (c a), LiftT a) => Quoted (c :: k -> Constraint) (a :: k)
instance (CodeC (c a), LiftT a) => Quoted c a

sgsappend ::
  (IsProductType a xs, All (Quoted Semigroup) xs) =>
  Code a -> Code a -> Code a
sgsappend c1 c2 =
  productTypeFrom c1 $ \ a1 -> productTypeFrom c2 $ \ a2 ->
    productTypeTo
      (czipWith_NP @(Quoted Semigroup)
        (mapCCC [|| (<>) ||]) a1 a2
      )

sgsappend' ::
  (IsProductType a xs, All (Quoted Semigroup) xs) =>
  Code (a -> a -> a)
sgsappend' =
  [|| \ a1 a2 -> $$(sgsappend [|| a1 ||] [|| a2 ||]) ||]

mapCCC :: LiftT c => Code (a -> b -> c) -> C a -> C b -> C c
mapCCC op (C a) (C b) = C [|| $$op $$a $$b ||]

class NFData a where
  rnf :: a -> ()

sgrnf ::
  (Generic a, All (All (Quoted NFData)) (Description a)) =>
  Code a -> Code ()
sgrnf c =
  from c $ \ a ->
    foldr (\ x r -> [|| $$x `seq` $$r ||]) [|| () ||]
      (collapse_SOP (cmap_SOP @(Quoted NFData) (mapCK [|| rnf ||]) a))

mapCK :: LiftT b => Code (a -> b) -> C a -> K (Code b) x
mapCK op (C a) = K [|| $$op $$a ||]

sgShowEnum ::
  IsEnumType a => NP (K String) (Description a) -> Code a -> Code String
sgShowEnum names c =
  enumTypeFrom c $ \ a ->
    liftTyped (collapse_NS (selectWith_NS const names a))

sgeq ::
  (Generic a, All (All (Quoted Eq)) (Description a)) =>
  Code a -> Code a -> Code Bool
sgeq c1 c2 =
  from c1 $ \ a1 -> from c2 $ \ a2 ->
  ccompare_SOP @(Quoted Eq)
    [|| False ||]
    (\ xs1 xs2 -> sand (collapse_NP (czipWith_NP @(Quoted Eq) (mapCCK [|| (==) ||]) xs1 xs2)))
    [|| False ||]
    a1 a2

mapCCK :: LiftT c => Code (a -> b -> c) -> C a -> C b -> K (Code c) x
mapCCK op (C a) (C b) = K [|| $$op $$a $$b ||]

sand :: [Code Bool] -> Code Bool
sand = foldr (\ x r -> [|| $$x && $$r ||]) [|| True ||]

data Foo = Foo [Int] Ordering String

instance Generic Foo where
  type Description Foo = '[ '[ [Int], Ordering, String ] ]

  from c k =
    [|| case $$c of
          Foo is o s -> $$(k (SOP (Z (C [|| is ||] :* C [|| o ||] :* C [|| s ||] :* Nil))))
    ||]

  to (SOP (Z (C is :* C o :* C s :* Nil))) =
    [|| Foo $$is $$o $$s ||]

data Tree a = Leaf a | Node (Tree a) (Tree a)

-- This is the first place where I'm truly worried by the LiftT constraint.
instance LiftT a => Generic (Tree a) where
  type Description (Tree a) = '[ '[ a ], '[ Tree a, Tree a ] ]

  from c k =
    [|| case $$c of
          Leaf a   -> $$(k (SOP (Z (C [|| a ||] :* Nil))))
          Node l r -> $$(k (SOP (S (Z (C [|| l ||] :* C [|| r ||] :* Nil)))))
    ||]

  to (SOP (Z (C a :* Nil)))            = [|| Leaf $$a ||]
  to (SOP (S (Z (C l :* C r :* Nil)))) = [|| Node $$l $$r ||]

data Pair a b = Pair a b

instance (LiftT a, LiftT b) => Generic (Pair a b) where
  type Description (Pair a b) = '[ '[ a, b ] ]

  from c k =
    [|| case $$c of
          Pair a b -> $$(k (SOP (Z (C [|| a ||] :* C [|| b ||] :* Nil))))
    ||]

  to (SOP (Z (C a :* C b :* Nil))) = [|| Pair $$a $$b ||]

instance Generic Ordering where
  type Description Ordering = '[ '[], '[], '[] ]

  from c k =
    [|| case $$c of
          LT -> $$(k (SOP (Z Nil)))
          EQ -> $$(k (SOP (S (Z Nil))))
          GT -> $$(k (SOP (S (S (Z Nil)))))
    ||]

  to (SOP (Z Nil))         = [|| LT ||]
  to (SOP (S (Z Nil)))     = [|| EQ ||]
  to (SOP (S (S (Z Nil)))) = [|| GT ||]

eqList :: (CodeC (Eq a), LiftT a) => Code ([a] -> [a] -> Bool)
eqList = [|| (==) ||]

data Person = Person { personId :: Int, name :: String, date :: Day }

data Day
class FromRow a where
  fromRow :: RowParser a
class FromField a
data RowParser a
field :: FromField a => RowParser a
field = undefined
instance Functor RowParser where fmap = undefined
instance Applicative RowParser where pure = undefined; (<*>) = undefined

sproductTypeToA ::
  (IsProductType a xs, CodeC (Applicative f)) =>
  NP (C :.: f) xs -> Code (f a)
sproductTypeToA =
  undefined

type family Curry r xs where
  Curry r '[]      = r
  Curry r (x : xs) = x -> Curry r xs

newtype SCurry r xs = SCurry { unSCurry :: (NP C xs -> Code r) -> Code (Curry r xs) }

-- I'm giving up on this function for now ...
-- GHC wants me to prove that `LiftT (Curry r xs)` for all xs.
--
{-
scurry_NP ::
  forall r xs . All LiftT xs => (NP C xs -> Code r) -> Code (Curry r xs)
scurry_NP =
{-
  unSCurry $ cpara_SList (Proxy @LiftT)
    (SCurry $ \ f -> f Nil)
    (\ (SCurry rec) -> SCurry $ \ f -> [|| \ x -> _ ||])
-}
  case sList :: SList xs of
    SNil  -> \ f -> f Nil
    SCons -> \ f -> [|| \ x -> $$(scurry_NP (\ xs -> f (C [|| x ||] :* xs))) ||]
-}

sgfromRow ::
  (IsProductType a xs, All (Quoted FromField) xs) =>
  Code (RowParser a)
sgfromRow =
  sproductTypeToA
    (cpure_NP @(Quoted FromField) (Comp (C [|| field ||])))
