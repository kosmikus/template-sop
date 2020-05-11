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
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Lib.Internal
import Unsafe.Coerce


type Code a = Q (TExp a)
type CodeF = Q :.: TExp

data NP (f :: k -> Type) :: [k] -> Type where
  Nil :: NP f '[]
  (:*) :: (LiftT f, LiftT x) => f x -> NP f xs -> NP f (x : xs)

data NPG (f :: k -> Type) :: [k] -> Type where
  NilG :: NPG f '[]
  (:**) :: f x -> NPG f xs -> NPG f (x : xs)

infixr 5 :*

data NS (f :: k -> Type) :: [k] -> Type where
  Z :: (LiftT x) => f x -> NS f (x : xs)
  S :: (LiftT xs, LiftT x) => NS f xs -> NS f (x : xs)

newtype (f :.: g) x = Comp { unComp :: f (g x) }

class (f (g x)) => (f `Compose` g) x
instance (f (g x)) => (f `Compose` g) x
infixr 9 `Compose`

class (f x, g x) => (f `And` g) x
instance (f x, g x) => (f `And` g) x
infixl 7 `And`


newtype SOP (f :: k -> Type) (xss :: [[k]]) = SOP { unSOP :: NS (NP f) xss }
newtype POP (f :: k -> Type) (xss :: [[k]]) = POP { unPOP :: NP (NP f) xss }

-- build :: (forall r . (a -> r -> r) -> r -> r) -> [a]

ocollapse_NP :: NP (K a) xs -> [a]
ocollapse_NP Nil         = []
ocollapse_NP (K x :* xs) = x : ocollapse_NP xs

collapse_NP :: LiftT a => NP (K (Code a)) xs -> Code [a]
collapse_NP = buildlist . ocollapse_NP

--buildlist :: _ => [Code a] -> Code [a]
--buildlist xs =
--  [|| build (\ cons nil -> $$(list [|| cons ||] [|| nil ||] xs)) ||]
--
buildlist :: LiftT a => [Code a] -> Code [a]
buildlist xs = list [|| (:) ||] [|| [] ||] xs

list :: LiftT r => Code (a -> r -> r) -> Code r -> [Code a] -> Code r
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

--ns :: (CodeC (LiftT xs), LiftT f) => NS (CodeF :.: f) xs -> Code (NS f xs)
--ns (Z (Comp (Comp c))) = [|| Z $$c ||]
--ns (S x)               = [|| S $$(ns x) ||]

collapse_NS :: NS (K a) xs -> a
collapse_NS (Z (K a)) = a
collapse_NS (S y)     = collapse_NS y

map_NP :: (LiftT g) => (forall x . LiftT x => f x -> g x) -> NP f xs -> NP g xs
map_NP f Nil       = Nil
map_NP f (x :* xs) = f x :* map_NP f xs

cmap_NP :: forall c f g xs . (LiftT g, All c xs) => (forall x . c x => f x -> g x) -> NP f xs -> NP g xs
cmap_NP f Nil       = Nil
cmap_NP f (x :* xs) = f x :* cmap_NP @c f xs

map_NS :: (forall x . f x -> g x) -> NS f xs -> NS g xs
map_NS f (Z x) = Z (f x)
map_NS f (S y) = S (map_NS f y)

cmap_NS :: forall c f g xs . All c xs => (forall x . c x => f x -> g x) -> NS f xs -> NS g xs
cmap_NS f (Z x) = Z (f x)
cmap_NS f (S y) = S (cmap_NS @c f y)

map_SOP :: (LiftT g) => (forall x . f x -> g x) -> SOP f xss -> SOP g xss
map_SOP f (SOP x) = SOP (map_NS (map_NP f) x)

cmap_SOP :: forall c f g xss . (LiftT g, All (All c) xss) => (forall x . c x => f x -> g x) -> SOP f xss -> SOP g xss
cmap_SOP f (SOP x) = SOP (cmap_NS @(All c) (cmap_NP @c f) x)

{-
sop :: SOP CodeF xss -> Code (SOP I xss)
sop (SOP x) = [|| SOP $$(ns (map_NS (\ y -> Comp (Comp (map_NP Comp y))) x)) ||]
-}

collapse_SOP :: LiftT a => SOP (K (Code a)) xss -> Code [a]
collapse_SOP (SOP x) = [|| $$(collapse_NS (map_NS (K . collapse_NP) x)) ||]


data B = MkB { getInt :: Int, getCh :: Char, getBool :: Bool }

data C = C1 | C2 | C3 | C4 | C5
  deriving (Show, Lift)

instance HasDatatypeInfo C where
  datatypeInfo = [("C1", 0), ("C2", 0), ("C3", 0), ("C4", 0), ("C5", 0)]

instance Generic C where
  type Description C = '[ '[], '[], '[], '[], '[] ]

  oto (SOP (Z Nil)) = C1
  oto (SOP (S (Z Nil))) = C2
  oto (SOP (S (S (Z Nil)))) = C3
  oto (SOP (S (S (S (Z Nil))))) = C4
  oto (SOP (S (S (S (S (Z Nil)))))) = C5

  to (SOP (Z Nil)) = [|| C1 ||]
  to (SOP (S (Z Nil))) = [|| C2 ||]
  to (SOP (S (S (Z Nil)))) = [|| C3 ||]
  to (SOP (S (S (S (Z Nil))))) = [|| C4 ||]
  to (SOP (S (S (S (S (Z Nil)))))) = [|| C5 ||]

  from a k =
    [|| case $$a of
          C1 -> $$(k (SOP (Z Nil)))
          C2 -> $$(k (SOP (S (Z Nil))))
          C3 -> $$(k (SOP (S (S (Z Nil)))))
          C4 -> $$(k (SOP (S (S (S (Z Nil))))))
          C5 -> $$(k (SOP (S (S (S (S (Z Nil)))))))
    ||]

{-
fromA :: A -> SOP I '[ '[Int, Char, Bool], '[Double] ]
fromA (MkA1 i c b) = SOP (Z (I i :* I c :* I b :* Nil))
fromA (MkA2 d)     = SOP (S (Z (I d :* Nil)))
-}

fromA1 :: Code Int -> Code Char -> Code Bool -> SOP CodeF '[ '[Int, Char, Bool], '[Double] ]
fromA1 i c b = SOP (Z (Comp i :* Comp c :* Comp b :* Nil))

fromA2 :: Code Double -> SOP CodeF '[ '[Int, Char, Bool], '[Double] ]
fromA2 d = SOP (S (Z (Comp d :* Nil)))


data A = MkA1 Int Char Bool | MkA2 Double

fromA :: LiftT r => Code A -> (SOP CodeF '[ '[Int, Char, Bool], '[Double] ] -> Code r) -> Code r
fromA a k =
  [|| case $$a of
        MkA1 i c b -> $$(k (fromA1 [|| i ||] [|| c ||] [|| b ||]))
        MkA2 d     -> $$(k (fromA2 [|| d ||]))
  ||]

class LiftT a => Generic a where
  type Description a :: [[Type]]
  ofrom :: a -> SOP I (Description a)
  from :: LiftT r => Code a -> (SOP CodeF (Description a) -> Code r) -> Code r
  oto :: SOP I (Description a) -> a
  to :: SOP CodeF (Description a) -> Code a

genFrom :: forall a r . (HasDatatypeInfo a, Generic a) =>
        ExpQ --Code (Code a -> (SOP CodeF (Description a) -> Code r) -> Code r)
genFrom =
  let
--    fake = oto (pure_NP (I undefined))

      dtinfo = datatypeInfo @a

  in
    [| \a k ->
          caseE a (zipWith (mkMatches k) [0..] dtinfo) |]

--create :: Int -> [ExpQ] -> SOP CodeF (Description a)
--create k vs = SOP (genI k (foldr (\a b -> unsafeCoerce (Comp (unsafeTExpCoerce a) :* b)) Nil vs))


--genI :: LiftT x => Int -> f x -> NS f xs
--genI 0 b = unsafeCoerce ( Z b )
--genI n b = unsafeCoerce ( S (genI (n - 1) b))

--mkMatches :: (SOP CodeF xs -> ExpQ) -> Int -> (String, Int) -> MatchQ
--mkMatches k j (s, i) = match (conP (mkName s) [varP $ mkName ("a" ++ show i) | i <- [1..i]])
--                          (normalB (k (unsafeCoerce $ create j [varE $ mkName ("a" ++ show i) | i <- [1..i]]) ))
--                          []

class HasDatatypeInfo a where
  datatypeInfo :: [(String, Int)]

{-
from' :: forall a r . Generic a => Code a -> (SOP CodeF (Description a) -> Code r) -> Code r
from' ca k =
  [|| let
        go :: SOP I xss -> SOP CodeF xss
        go = undefined
      in
        $$(k (go (ofrom $$ca)))
  ||]
-}

fromB :: Code B -> NP CodeF '[Int, Char, Bool]
fromB cb = Comp [|| getInt $$cb ||] :* Comp [|| getCh $$cb ||] :* Comp [|| getBool $$cb ||] :* Nil

data SList (xs :: [k]) :: Type where
  SNil  :: SList '[]
  SCons :: (LiftT x, LiftT xs, LiftT k,  SListI xs) => SList (x : xs)

class (LiftT k, LiftT xs) => SListI (xs :: [k]) where
  sList :: SList xs

instance LiftT k => SListI ('[] :: [k]) where
  sList = SNil

instance (LiftT x, LiftT xs, LiftT k, SListI xs) => SListI ((x : xs) :: [k]) where
  sList = SCons @x @xs @k

class (AllF c xs, SListI xs) => All (c :: k -> Constraint) xs
instance (AllF c xs, SListI xs) => All c xs

type family AllF (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllF c '[] = ()
  AllF c (x : xs) = (c x, SListI xs, AllF c xs)

newtype K a b = K { unK :: a }
newtype I a   = I { unI :: a }

{-
pureK :: forall xs a . (Lift a, SListI xs) => a -> Code (NP (K a) xs)
pureK p =
  case sList @_ @xs of
    SNil  -> [|| Nil ||]
    SCons -> [|| K p :* $$(pureK p) ||]
    -}

newtype  Fun0   f   = Fun0  { unFun0  :: forall x . f x }
newtype  Fun1   f g = Fun1  { unFun1  :: forall x . f x -> g x }
newtype CFun0 c f   = CFun0 { unCFun0 :: forall x . c x => f x }

data (f -.-> g) x where
  Fn :: (LiftT f, LiftT g, LiftT x) => (f x -> g x) -> (f -.-> g) x

apFn (Fn f) = f

{-
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
    -}

ocpure_NP :: forall c xs f . (LiftT f, All c xs, SListI xs) => (forall x . c x => f x) -> NP f xs
ocpure_NP p =
  case sList @_ @xs of
    SNil  -> Nil
    SCons -> p :* ocpure_NP @c p

cpure_POP :: forall k (c :: k -> Constraint) xss f . (LiftT f, LiftT k, All (All c) xss, SListI xss) => (forall x . c x => f x) -> POP f xss
cpure_POP p =
  POP (ocpure_NP @(All c) (ocpure_NP @c p))

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

capply :: LiftT b => Code (a -> b) -> Code a -> Code b
capply cf cx = [|| $$cf $$cx ||]

transform2 :: forall k g (x :: k) f . (LiftT f, LiftT k, LiftT g, LiftT x) => Code (Fun1 f g) -> Code (f x) -> Code (g x)
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
--  let faulty :: Code a -> Code Int
--      faulty x = from x (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||])))
--  in
  [|| \ a -> $$(  from [|| a ||] (capply [|| sum ||] . collapse_SOP . map_SOP (const (K [|| 1 ||])))) ||]

gshow :: forall a . (All (All LiftT) (Description a), Generic a, All (All (And LiftT (Compose CodeC Show))) (Description a)) => Code (a -> String)
gshow =
  let x v  = (from v (capply [|| concat ||] . collapse_SOP . cmap_SOP @(And LiftT (Compose CodeC Show)) (\ (Comp x) -> K (capply [|| show ||] x))))
  in [|| \ a -> $$(x [|| a ||]) ||]

type Injection (f :: k -> Type) (xs :: [k]) = f -.-> (K (NS f xs))

injections :: forall xs f. (LiftT f, SListI xs) => NP (Injection f xs) xs
injections = case sList :: SList xs of
  SNil   -> Nil
  SCons  -> Fn (K . Z) :* map_NP shiftInjection injections

shiftInjection :: forall k (x :: k) (f :: k -> *) xs a . (LiftT xs, LiftT k, LiftT x) => Injection f xs a -> Injection f (x ': xs) a
shiftInjection (Fn f) = Fn $ K . S . unK . f

ap_NP :: (LiftT f, LiftT g) => NP (f -.-> g) xs -> NP f xs -> NP g xs
ap_NP Nil       Nil       = Nil
ap_NP (f :* fs) (x :* xs) = apFn f x :* ap_NP fs xs

apInjs'_NP :: (LiftT f, SListI xs) => NP f xs -> NP (K (NS f xs)) xs
apInjs'_NP = ap_NP injections

apInjs_NP :: (LiftT f, SListI xs) => NP f xs -> [NS f xs]
apInjs_NP = ocollapse_NP . apInjs'_NP

apInjs_POP :: forall k (f :: k -> *) (xss :: [[k]]) . (LiftT k, LiftT f, SListI xss) => POP f xss -> [SOP f xss]
apInjs_POP = map SOP . apInjs_NP . unPOP

genum :: (Generic a, SListI (Description a), All ((~) '[]) (Description a)) => [a]
genum = oto <$> apInjs_POP (POP (ocpure_NP @((~) '[]) Nil))

liftT :: Lift a => a -> Code a
liftT = liftTyped

cgenum :: (Generic a, Lift a, SListI (Description a), All ((~) '[]) (Description a)) => Code [a]
cgenum = buildlist (to <$> apInjs_POP (POP (ocpure_NP @((~) '[]) Nil)))

data R = R { _ra :: A, _rb :: B, _rc :: C }

instance HasDatatypeInfo R where
  datatypeInfo = [("R", 3)]

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

npsetters :: forall xs f . (LiftT f, LiftT xs, SListI xs) => NP (Setter f xs) xs
npsetters = case sList :: SList xs of
  SNil  -> Nil
  SCons -> Setter (\ x (_ :* xs) -> x :* xs) :* map_NP shiftSetters npsetters

projections :: forall xs f . (LiftT f, SListI xs) => NP (Projection f xs) xs
projections = case sList :: SList xs of
  SNil  -> Nil
  SCons -> Fn (hd . unK) :* map_NP shiftProjection projections

hd :: NP f (x : xs) -> f x
hd (x :* _) = x

tl :: NP f (x : xs) -> NP f xs
tl (_ :* xs) = xs

unZ :: NS f '[ x ] -> f x
unZ (Z x) = x


shiftProjection :: forall a (a1 :: a) (x ::a) (f :: a -> *) (xs :: [a]) . (LiftT xs, LiftT a, LiftT x) => Projection f xs a1 -> Projection f (x ': xs) a1
shiftProjection (Fn f) = Fn $ f . K . tl . unK

shiftSetters ::  Setter f xs a -> Setter f (x : xs) a
shiftSetters (Setter f) = Setter (\ y (x :* xs) -> x :* f y xs)

np :: forall k (f :: k -> *) (xs :: [k]) . (LiftT k, All LiftT xs, LiftT f) => NP (CodeF :.: f) xs -> Code (NPG f xs)
np Nil                   = [|| NilG ||]
np (Comp (Comp c) :* cs) = [|| $$c :** $$(np cs) ||]

oggetters :: forall a x . (Generic a, Description a ~ '[ x ], SListI x) => NP ((->) a) x
oggetters = map_NP (\ f a -> unI (apFn f (K (unZ (unSOP (ofrom a)))))) projections

newtype Setter' s a = Setter' (a -> s -> s)

ogsetters :: forall s x . (CodeC (LiftT x), Generic s, Description s ~ '[ x ], SListI x) => NP (Setter' s) x
ogsetters = map_NP (\ (Setter f) -> Setter' (\ a s -> oto (SOP (Z (f (I a) (unZ (unSOP (ofrom s)))))))) npsetters

ggetters :: forall a x . (LiftT x, LiftT a,  All (All LiftT) (Description a),  Generic a, Description a ~ '[ x ], SListI x) => Code (NPG ((->) a) x)
ggetters =
  let faulty f x = (from x (unComp . apFn f . K . unZ . unSOP))
  in np (map_NP (\ f -> Comp (Comp [|| \ a -> $$(faulty f [|| a||]) ||])) projections)

gsetters :: forall s x . (LiftT x, All (All LiftT) (Description s), Generic s, Description s ~ '[ x ], SListI x) => Code (NPG (Setter' s) x)
gsetters =
  let faulty f x a = (from x (\ sop -> to (SOP (Z (f (Comp a) (unZ (unSOP sop)))))))
  in np (map_NP (\ (Setter f) -> Comp (Comp [|| Setter' (\ a s -> $$(faulty f [|| s ||] [|| a ||])) ||])) npsetters)

ogcompare :: (Generic a, All (All Ord) (Description a)) => a -> a -> Ordering
ogcompare x y = go (unSOP (ofrom x)) (unSOP (ofrom y))
  where
    go :: forall xss . All (All Ord) xss => NS (NP I) xss -> NS (NP I) xss -> Ordering
    go (Z x) (Z y) = mconcat (ocollapse_NP (czipWith_NP @Ord (\ (I a) (I b) -> K (compare a b)) x y))
    go (Z _) (S _) = LT
    go (S _) (Z _) = GT

czipWith_NP :: forall c xs f g h . (LiftT h, All c xs) => (forall x . c x => f x -> g x -> h x) -> NP f xs -> NP g xs -> NP h xs
czipWith_NP p  Nil Nil = Nil
czipWith_NP p (f :* fs) (g :* gs) = p f g :* czipWith_NP @c p fs gs


select :: NP (f -.-> g) xs -> NS f xs -> NS g xs
select (f :* _)  (Z x) = Z (apFn f x)
select (_ :* fs) (S y) = S (select fs y)

ogcase :: (Generic a) => NP (NP I -.-> K r) (Description a) -> a -> r
ogcase table a = collapse_NS (select table (unSOP (ofrom a)))

{-
gcase :: (LiftT r, Generic a) => NP (CodeF :.: (NP I -.-> K r)) (Description a) -> Code (a -> r)
gcase table =
  [|| \ a -> $$(from [|| a ||] (\ a' -> collapse_NS (select (map_NP (capply' . unComp . unComp) table) (unSOP a')))) ||]
  -}


{-
capply' :: (LiftT r, LiftT x) => Code ((NP I -.-> K r) x) -> (NP CodeF -.-> K (Code r)) x
capply' cf = Fn (\ npc -> K [|| unK (apFn $$cf $$(np (map_NP (\ (Comp x) -> Comp (Comp (capply [|| I ||] x))) npc))) ||])
-}

{-
unspillNP :: forall k (xs :: [k]) f r . (LiftT k, LiftT f, LiftT r, LiftT xs, SListI xs, CodeC (SListI xs)) => Code (NP f xs) -> (NP (CodeF :.: f) xs -> Code r) -> Code r
unspillNP cnp k = case sList :: SList xs of
  SNil  -> k Nil
  SCons ->
    [|| elimNPCons $$cnp (\ x xs -> $$(unspillNP [|| xs ||] (\ xs' -> k (Comp (Comp [|| x ||]) :* xs')))) ||]
-}


elimNPCons :: SListI xs => NP f (x : xs) -> (f x -> NP f xs -> r) -> r
elimNPCons (x :* xs) k = k x xs

type family Curry (xs :: [Type]) (r :: Type) :: Type where
  Curry '[] r = r
  Curry (x : xs) r = x -> Curry xs r

curryNP :: forall xs r . SListI xs => (NP I xs -> r) -> Curry xs r
curryNP k = case sList :: SList xs of
  SNil -> k Nil
  SCons -> \ x -> curryNP (\ xs -> k (I x :* xs))

instance Generic A where
  type Description A = '[ '[Int, Char, Bool], '[Double] ]
  from = fromA

instance HasDatatypeInfo A where
  datatypeInfo = [("MkA1", 3), ("MkA2", 1)]
