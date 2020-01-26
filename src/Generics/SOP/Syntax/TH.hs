{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Generics.SOP.Syntax.TH (deriveGenericSyntax) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Generics.SOP
import Data.List (foldl')
import Control.Monad (unless)
import Language.Haskell.TH.Lift () -- Lift Name

import qualified Language.Haskell.TH.Datatype as TH

import Generics.SOP.Syntax

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Derive 'GenericSyntax' type-class instance.
deriveGenericSyntax :: Name -> Q [Dec]
deriveGenericSyntax dn = do
    di@TH.DatatypeInfo
        { TH.datatypeName = name
        , TH.datatypeInstTypes = instTypes
        }  <- TH.reifyDatatype dn

    let typ :: TypeQ
        typ = appsT name (map (return . unSigType) instTypes)

    inst <- instanceD
            (cxt [])
            [t| GenericSyntax $typ |]
            [ funD 'sto   [ clause [] (normalB $ deriveSto di) [] ]
            , funD 'sfrom [ clause [] (normalB $ deriveSfrom di) [] ]
            ]

    return [inst]

-------------------------------------------------------------------------------
-- To
-------------------------------------------------------------------------------

deriveSto :: TH.DatatypeInfo -> Q Exp
deriveSto di = do
    let TH.DatatypeInfo
           { TH.datatypeCons = cons
           } = di

    arg <- newName "sop"

    lamE [varP arg] (caseE (varE arg) (go id cons))
  where
    go :: (PatQ -> PatQ) -> [TH.ConstructorInfo] -> [MatchQ]
    go br [] = return $ do
        x <- newName "x"
        match (conP 'SOP [ br (varP x) ]) (normalB (caseE (varE x) [])) []

    go br (c:cs) = mkClause br c : go (\p -> conP 'S [br p]) cs

    mkClause :: (PatQ -> PatQ) -> TH.ConstructorInfo -> MatchQ
    mkClause br c = do
        (n, ts) <- conInfo c
        vars    <- traverse newName (zipWith (\i _ -> "_x" ++ show i) [1 :: Int ..] ts)
        match
            (conP 'SOP [ br $ conP 'Z [ npP [ conP 'Comp [varP v] | v <- vars ] ] ])
            (normalB $
                foldl' (\f x -> [| sapply $f $x |])
                    ([| unsafeTExpCoerce |] `appE` ([| conE |] `appE` lift n))
                    [ varE v | v <- vars])
            []

-------------------------------------------------------------------------------
-- From
-------------------------------------------------------------------------------

deriveSfrom :: TH.DatatypeInfo -> Q Exp
deriveSfrom di = do
    let TH.DatatypeInfo
           { TH.datatypeCons = cons
           } = di

    val <- newName "val"
    k   <- newName "_k" -- avoids unused warning

    lamE [varP val, varP k] ([| unsafeTExpCoerce |] `appE` foldl' appE [| caseE |]
        [ [| unTypeQ |] `appE` varE val
        , listE $ go (varE k) (\e -> [| Z $e |]) cons
        ])
  where
    go :: Q Exp -> (Q Exp -> Q Exp) -> [TH.ConstructorInfo] -> [ExpQ]
    go _ _  []     = []
    go k br (c:cs) = mkClause k br c : go k (\e -> [| S $(br e) |]) cs

    mkClause :: Q Exp -> (Q Exp -> Q Exp) -> TH.ConstructorInfo -> ExpQ
    mkClause k br c = do
        (n, ts) <- conInfo c
        let varNames = zipWith (\i _ -> "_x" ++ show i) [1 :: Int ..] ts
        vars <- traverse newName varNames

        let kontArg :: ExpQ
            kontArg = br $ npE
                [ [| Comp (unsafeTExpCoerce (varE $(varE v))) |]
                | v <- vars
                ]

        doE $ [ bindS (varP v) [| newName $(stringE s) |] | (v, s) <- zip vars varNames ] ++
            [ noBindS $ foldl' appE [| match |]
                [ foldl' appE [| conP |]
                    [ lift n
                    , listE [ [| varP |] `appE` varE v | v <- vars ]
                    ]
                , [| normalB (unTypeQ ($k (SOP $kontArg))) |]
                , listE []
                ]
            ]

-------------------------------------------------------------------------------
-- 
-------------------------------------------------------------------------------


conInfo :: TH.ConstructorInfo -> Q (Name, [Q Type])
conInfo ci = checkForGADTs ci $
    return (TH.constructorName ci, map return (TH.constructorFields ci))

checkForGADTs :: TH.ConstructorInfo -> Q a -> Q a
checkForGADTs ci q = do
  unless (null $ TH.constructorVars ci)    $ fail "Existentials not supported"
  unless (null $ TH.constructorContext ci) $ fail "GADTs not supported"
  q

appsT :: Name -> [Q Type] -> Q Type
appsT n = foldl' appT (conT n)

unSigType :: Type -> Type
unSigType (SigT t _) = t
unSigType t          = t

npE :: [Q Exp] -> Q Exp
npE []     = [| Nil |]
npE (e:es) = [| $e :* $(npE es) |]

-- Like npE, but construct a pattern instead
npP :: [Q Pat] -> Q Pat
npP []     = conP 'Nil []
npP (p:ps) = conP '(:*) [p, npP ps]
