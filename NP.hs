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

newtype SOP (f :: k -> Type) (xss :: [[k]]) = SOP { unSOP :: NS (NP f) xss }
newtype POP (f :: k -> Type) (xss :: [[k]]) = POP { unPOP :: NP (NP f) xss }

-- build :: (forall r . (a -> r -> r) -> r -> r) -> [a]

ocollapse_NP :: NP (K a) xs -> [a]
ocollapse_NP Nil         = []
ocollapse_NP (K x :* xs) = x : ocollapse_NP xs

collapse_NP :: NP (K (Code a)) xs -> Code [a]
collapse_NP = buildlist . ocollapse_NP

buildlist :: [Code a] -> Code [a]
buildlist xs =
  [|| build (\ cons nil -> $$(list [|| cons ||] [|| nil ||] xs)) ||]

list :: Code (a -> r -> r) -> Code r -> [Code a] -> Code r
list cons nil []       = nil
list cons nil (x : xs) = [|| $$cons $$x $$(list cons nil xs) ||]

{-
collapse_NP :: NP (K (Code a)) xs -> Code [a]
collapse_NP np =
  [|| build (\ cons nil -> $$(collapse_NP' [|| cons ||] [|| nil ||] np)) ||]

collapse_NP' :: Code (a -> r -> r) -> Code r -> NP (K (Code a)) xs -> Code r
collapse_NP' cons nil Nil         = nil
collapse_NP' cons nil (K a :* xs) = [|| $$cons $$a $$(collapse_NP' cons nil xs) ||]
-}

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

{-
sop :: SOP CodeF xss -> Code (SOP I xss)
sop (SOP x) = [|| SOP $$(ns (map_NS (\ y -> Comp (Comp (map_NP Comp y))) x)) ||]
-}

collapse_SOP :: SOP (K (Code a)) xss -> Code [a]
collapse_SOP (SOP x) = [|| $$(collapse_NS (map_NS (K . collapse_NP) x)) ||]

data A = MkA1 Int Char Bool | MkA2 Double

data B = MkB { getInt :: Int, getCh :: Char, getBool :: Bool }

data C = C1 | C2 | C3
  deriving (Show, Lift)

instance Generic C where
  type Description C = '[ '[], '[], '[] ]

  oto (SOP (Z Nil)) = C1
  oto (SOP (S (Z Nil))) = C2
  oto (SOP (S (S (Z Nil)))) = C3

  to (SOP (Z Nil)) = [|| C1 ||]
  to (SOP (S (Z Nil))) = [|| C2 ||]
  to (SOP (S (S (Z Nil)))) = [|| C3 ||]

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
  ofrom :: a -> SOP I (Description a)
  from :: Code a -> (SOP CodeF (Description a) -> Code r) -> Code r
  oto :: SOP I (Description a) -> a
  to :: SOP CodeF (Description a) -> Code a

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

newtype K a b = K { unK :: a }
newtype I a   = I { unI :: a }

pureK :: forall xs a . (Lift a, SListI xs) => a -> Code (NP (K a) xs)
pureK p =
  case sList @_ @xs of
    SNil  -> [|| Nil ||]
    SCons -> [|| K p :* $$(pureK p) ||]

newtype  Fun0   f   = Fun0  { unFun0  :: forall x . f x }
newtype  Fun1   f g = Fun1  { unFun1  :: forall x . f x -> g x }
newtype CFun0 c f   = CFun0 { unCFun0 :: forall x . c x => f x }

newtype (f -.-> g) x = Fn { apFn :: f x -> g x }

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

ocpure_NP :: forall c xs f . (All c xs, SListI xs) => (forall x . c x => f x) -> NP f xs
ocpure_NP p =
  case sList @_ @xs of
    SNil  -> Nil
    SCons -> p :* ocpure_NP @c p

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

type Injection (f :: k -> Type) (xs :: [k]) = f -.-> (K (NS f xs))

injections :: forall xs f. SListI xs => NP (Injection f xs) xs
injections = case sList :: SList xs of
  SNil   -> Nil
  SCons  -> Fn (K . Z) :* map_NP shiftInjection injections

shiftInjection :: Injection f xs a -> Injection f (x ': xs) a
shiftInjection (Fn f) = Fn $ K . S . unK . f

ap_NP :: NP (f -.-> g) xs -> NP f xs -> NP g xs
ap_NP Nil       Nil       = Nil
ap_NP (f :* fs) (x :* xs) = apFn f x :* ap_NP fs xs

apInjs'_NP :: SListI xs => NP f xs -> NP (K (NS f xs)) xs
apInjs'_NP = ap_NP injections

apInjs_NP :: SListI xs => NP f xs -> [NS f xs]
apInjs_NP = ocollapse_NP . apInjs'_NP

apInjs_POP :: SListI xss => POP f xss -> [SOP f xss]
apInjs_POP = map SOP . apInjs_NP . unPOP

genum :: (Generic a, SListI (Description a), All ((~) '[]) (Description a)) => [a]
genum = oto <$> apInjs_POP (POP (ocpure_NP @((~) '[]) Nil))

liftT :: Lift a => a -> Code a
liftT = unsafeTExpCoerce . lift

cgenum :: (Generic a, Lift a, SListI (Description a), All ((~) '[]) (Description a)) => Code [a]
cgenum = buildlist (to <$> apInjs_POP (POP (ocpure_NP @((~) '[]) Nil)))

data R = R { _ra :: A, _rb :: B, _rc :: C }

instance Generic R where
  type Description R = '[ '[ A, B, C ] ]

  from r k =
    [|| case $$r of
           R ra rb rc -> $$(k (SOP (Z (Comp [|| ra ||] :* Comp [|| rb ||] :* Comp [|| rc ||] :* Nil))))
    ||]

  to (unZ . unSOP  -> (Comp ra :* Comp rb :* Comp rc :* Nil)) = [|| R $$ra $$rb $$rc ||]

ra :* rb :* rc :* Nil = oggetters @R

type Projection (f :: k -> *) (xs :: [k]) = K (NP f xs) -.-> f

-- a -> s -> s
-- f -.-> K (NP f xs) -.-> K (NP f xs)

newtype Setter (f :: k -> Type) (xs :: [k]) a = Setter (f a -> NP f xs -> NP f xs)

npsetters :: forall xs f . SListI xs => NP (Setter f xs) xs
npsetters = case sList :: SList xs of
  SNil  -> Nil
  SCons -> Setter (\ x (_ :* xs) -> x :* xs) :* map_NP shiftSetters npsetters

projections :: forall xs f . SListI xs => NP (Projection f xs) xs
projections = case sList :: SList xs of
  SNil  -> Nil
  SCons -> Fn (hd . unK) :* map_NP shiftProjection projections

hd :: NP f (x : xs) -> f x
hd (x :* _) = x

tl :: NP f (x : xs) -> NP f xs
tl (_ :* xs) = xs

unZ :: NS f '[ x ] -> f x
unZ (Z x) = x

shiftProjection :: Projection f xs a -> Projection f (x ': xs) a
shiftProjection (Fn f) = Fn $ f . K . tl . unK

shiftSetters :: Setter f xs a -> Setter f (x : xs) a
shiftSetters (Setter f) = Setter (\ y (x :* xs) -> x :* f y xs)

np :: NP (CodeF :.: f) xs -> Code (NP f xs)
np Nil                   = [|| Nil ||]
np (Comp (Comp c) :* cs) = [|| $$c :* $$(np cs) ||]

oggetters :: forall a x . (Generic a, Description a ~ '[ x ], SListI x) => NP ((->) a) x
oggetters = map_NP (\ f a -> unI (apFn f (K (unZ (unSOP (ofrom a)))))) projections

newtype Setter' s a = Setter' (a -> s -> s)

ogsetters :: forall s x . (Generic s, Description s ~ '[ x ], SListI x) => NP (Setter' s) x
ogsetters = map_NP (\ (Setter f) -> Setter' (\ a s -> oto (SOP (Z (f (I a) (unZ (unSOP (ofrom s)))))))) npsetters

ggetters :: forall a x . (Generic a, Description a ~ '[ x ], SListI x) => Code (NP ((->) a) x)
ggetters = np (map_NP (\ f -> Comp (Comp [|| \ a -> $$(from [|| a ||] (unComp . apFn f . K . unZ . unSOP)) ||])) projections)

gsetters :: forall s x . (Generic s, Description s ~ '[ x ], SListI x) => Code (NP (Setter' s) x)
gsetters = np (map_NP (\ (Setter f) -> Comp (Comp [|| Setter' (\ a s -> $$(from [|| s ||] (\ sop -> to (SOP (Z (f (Comp [|| a ||]) (unZ (unSOP sop)))))))) ||])) npsetters)
