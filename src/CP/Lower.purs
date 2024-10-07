module Language.CP.Lower where

import Prelude

import Control.Alternative ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, evalRWST, execRWST, modify, runRWST)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Data.Array (all, find)
import Data.Bifunctor (bimap, lmap, rmap)
import Data.Either (Either)
import Data.List (List(..), concat, elemIndex, foldl, intercalate, notElem, nub, sort, (:))
import Data.Map (Map, empty, fromFoldable, lookup)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, isJust, maybe)
import Data.String (Replacement(..), Pattern(..), replaceAll, toLower)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (REPLState)
import Language.CP.Subtyping (isTopLike, split, (===))
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Common as Op
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.RcdIR as R
import Language.CP.Util ((<+>))
import Partial.Unsafe (unsafeCrashWith)

type Lowering = RWST Ctx Unit Int (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           , inTrait   :: Boolean
           }

emptyCtx :: Ctx
emptyCtx = { tmBindEnv: empty
           , tyBindEnv: empty
           , inTrait: false
           }

fromState :: REPLState -> Ctx
fromState st = emptyCtx { tmBindEnv = fromFoldable $ rmap fst <$> st.tmBindings }

runLowering :: C.Tm -> Ctx -> Either String (R.Tm /\ C.Ty)
runLowering e ctx = runExcept $ fst <$> evalRWST (infer e) ctx 0

infer :: C.Tm -> Lowering (R.Tm /\ C.Ty)    -- R.Tm here should only be R.Rcd
-- TODO: all core terms should be lowered to some forms of records
--       e.g. 42 ~~> { "int": 42 }
infer (C.TmInt i) = pure $ Tuple (R.TmRcd (R.Fld (indexOf C.TyInt) (R.TmInt i) : Nil)) C.TyInt
infer (C.TmDouble n) = pure $ Tuple (R.TmRcd (R.Fld (indexOf  C.TyDouble) (R.TmDouble n) : Nil)) C.TyDouble
infer (C.TmBool b) = pure $ Tuple (R.TmRcd (R.Fld (indexOf C.TyBool) (R.TmBool b) : Nil)) C.TyBool
infer C.TmUnit = pure $ Tuple (R.TmRcd (R.Fld (indexOf C.TyUnit) R.TmUnit : Nil)) C.TyUnit
infer C.TmTop = pure topRcd
infer C.TmUndefined = pure $ Tuple (R.TmRcd (R.Fld (indexOf C.TyBot) R.TmUndefined : Nil)) C.TyBot
infer (C.TmUnary op t) = do
    t' /\ ty' <- infer t
    pure $ (R.TmRcd (R.Fld (indexOf ty') (R.TmUnary op t') : Nil)) /\ ty'
infer (C.TmBinary (Op.Arith op) t1 t2) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    pure $ (R.TmRcd (R.Fld (indexOf ty1) (R.TmBinary (Op.Arith op) t1' t2') : Nil)) /\ ty1
infer (C.TmBinary (Op.Comp op) t1 t2) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    pure $ (R.TmRcd (R.Fld (indexOf C.TyBool) (R.TmBinary (Op.Comp op) t1' t2') : Nil)) /\ C.TyBool
infer (C.TmBinary (Op.Logic op) t1 t2) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    pure $ (R.TmRcd (R.Fld (indexOf ty1) (R.TmBinary (Op.Logic op) t1' t2') : Nil)) /\ ty1
infer (C.TmBinary Op.Append t1 t2) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    pure $ (R.TmRcd (R.Fld (indexOf ty1) (R.TmBinary Op.Append t1' t2') : Nil)) /\ ty1
infer (C.TmBinary Op.Index t1 t2) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    case ty1 of
        C.TyArray ty' -> pure $ (R.TmRcd (R.Fld (indexOf ty') (R.TmBinary Op.Index t1' t2') : Nil)) /\ ty'
        _ -> unsafeCrashWith $ "CP.Lower.infer"
infer (C.TmIf t1 t2 t3) = do
    t1' /\ ty1 <- infer t1
    t2' /\ ty2 <- infer t2
    t3' /\ ty3 <- infer t3
    pure $ if isTopLike ty2
        then (R.TmRcd Nil) /\ C.TyTop
        else (R.TmRcd (R.Fld (indexOf ty2) (R.TmIf t1' t2' t3') : Nil)) /\ ty2
infer (C.TmVar n) = Tuple (R.TmVar n) <$> lookupTmBind n
infer (C.TmApp t1 t2 _) = do
    r1 <- infer t1
    r2 <- infer t2
    distApp r1 r2
infer (C.TmAbs n tm ta tt _ _) | isTopLike tt = pure topRcd
infer (C.TmAbs n tm ta tt f1 f2) = do
    r <- addTmBind n ta $ check tm tt
    let aty = C.TyArrow ta tt false
    pure $ R.TmRcd (R.Fld (indexOf aty) (R.TmAbs n r ta tt f1 f2) : Nil) /\ aty
infer (C.TmFix n tm ty) = do
    t' /\ ty' <- addTmBind n ty $ infer tm
    pure $ R.TmRcd (R.Fld (indexOf ty) (R.TmFix n t' ty) : Nil) /\ ty
infer (C.TmAnno tm ty) = do
    t' <- check tm ty
    pure $ t' /\ ty
infer (C.TmMerge a b) = do
  a' /\ ta <- infer a
  b' /\ tb <- infer b
  (_ /\ C.TyAnd ta tb) <$> rcdCons a' b' 
-- infer (C.TmSwitch t n br) = unsafeCrashWith $ "CP.Lower.infer:"
infer (C.TmRcd l ty t) | isTopLike ty = pure topRcd
infer (C.TmRcd l ty t) = do
    a /\ ta <- infer t
    let r = R.TmRcd (R.Fld l a : Nil)
    let rt = C.TyRcd l ta
    pure $ R.TmRcd (R.Fld (indexOf rt) r : Nil) /\ rt
infer (C.TmPrj t l) = do
    et <- infer t
    distProj et l
-- infer (C.TmTApp tm ty) = unsafeCrashWith $ "CP.Lower.infer:"
-- infer (C.TmTAbs n _ tm _ _) = unsafeCrashWith $ "CP.Lower.infer:"
-- todo
infer e = unsafeCrashWith $ "CP.Lower.infer:" <+> show e

check :: C.Tm -> C.Ty -> Lowering R.Tm
check tm ty = do
    tr@(tm' /\ ty') <- infer tm
    if ty' .=. ty 
        then pure tm'
        else tr <: ty

addTmBind :: forall a. Name -> C.Ty -> Lowering a -> Lowering a
addTmBind x t = local (\ctx -> ctx { tmBindEnv = Map.insert x t ctx.tmBindEnv })

lookupTmBind :: Name -> Lowering C.Ty
lookupTmBind n = do
    env <- asks (_.tmBindEnv)
    case lookup n env of
        Just ty -> pure ty
        Nothing -> throwError $ "Variable " <> n <> " not found"

freshVarName :: Lowering Name
freshVarName = do
  count <- modify (_ + 1)
  pure $ variable $ show count

indexOf :: C.Ty -> String
indexOf ty = case go Nil ty of
    Nil -> unsafeCrashWith $ "unreachable"
    t : Nil -> t
    ts -> "(" <> intercalate "&"  ts <> ")"
  where
    go :: List Name -> C.Ty -> List String
    go _ t | isBaseType t = toLower (show t) : Nil
    go as (C.TyArrow _ t _)  = pure $ "fun_" <>  flatTy (go as t)
    go as (C.TyForall a _ t) = pure $ "forall_" <> flatTy (go (a:as) t)
    go as (C.TyRcd l t)      = pure $ "rcd_" <> l <> ":" <> flatTy (go as t)
    go as (C.TyArray t)      = pure $ "array_" <> flatTy (go as t)
    go as (C.TyRef t)        = pure $ "ref_" <> flatTy (go as t)
    go as (C.TyVar a)        = case a `elemIndex` as of
                                 Just index -> show index : Nil
                                 Nothing -> ("${toIndex(" <> variable a <> ")}") : Nil  -- exposed codegen detail
    go as (C.TyRec a t)      = go (a:as) t
    go as (C.TyAnd a b)      = sort $ nub (go as a) <> (go as b)
    go _ t = unsafeCrashWith $ "cannot use as an index: " <> show t

    flatTy Nil = unsafeCrashWith $ "unreachable"
    flatTy (t : Nil) = t
    flatTy ts = "(" <> intercalate "&"  ts <> ")"
    -- -- a dirty string manipulation:
    isBaseType C.TyBool     = true
    isBaseType C.TyInt      = true
    isBaseType C.TyDouble   = true
    isBaseType C.TyString   = true
    isBaseType C.TyUnit     = true
    isBaseType C.TyBot      = true
    isBaseType _            = false

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")

flatten :: C.Ty -> Array C.Ty
flatten (C.TyAnd t1 t2) = flatten t1 <> flatten t2
flatten t | isTopLike t = []
          | otherwise   = [t]

equiv :: C.Ty -> C.Ty -> Boolean
equiv t1 t2 | isTopLike t1 && isTopLike t2 = true
equiv t1@(C.TyAnd _ _) t2 = let ts1 = flatten t1
                                ts2 = flatten t2 in
                            all (\t -> isJust $ find (t .=. _) ts2) ts1 &&
                            all (\t -> isJust $ find (t .=. _) ts1) ts2
equiv t1 t2@(C.TyAnd _ _) = equiv t2 t1
equiv (C.TyArrow t1 t2 _) (C.TyArrow t3 t4 _) = t1 .=. t3 && t2 .=. t4
equiv (C.TyRcd l1 t1) (C.TyRcd l2 t2) = l1 == l2 && t1 .=. t2
equiv (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) = td1 .=. td2 && t1 .=. C.tySubst a2 (C.TyVar a1) t2
equiv (C.TyRec a1 t1) (C.TyRec a2 t2) = t1 .=. C.tySubst a2 (C.TyVar a1) t2
equiv (C.TyArray t1) (C.TyArray t2) = t1 .=. t2
equiv (C.TyRef t1) (C.TyRef t2) = t1 .=. t2
equiv t1 t2 | t1 === t2 = true
            | otherwise = false

infix 4 equiv as .=.

distApp :: (R.Tm /\ C.Ty) -> (R.Tm /\ C.Ty) -> Lowering (R.Tm /\ C.Ty)
distApp (t1 /\ ty1) (t2 /\ ty2) | isTopLike ty1 = pure topRcd
distApp (t1 /\ C.TyAnd a b) (t2 /\ c) = do
    t3 /\ a' <- distApp (t1 /\ a) (t2 /\ c)
    t4 /\ b' <- distApp (t1 /\ b) (t2 /\ c)
    (_ /\ C.TyAnd a' b') <$> rcdCons t3 t4 
distApp (t1 /\ ta@(C.TyArrow a b _)) (t2 /\ c) | not (isTopLike b) = do
    t3 <- subtype (t2 /\ c) a
    t <- rcdFld (indexOf ta) t1
    pure $ R.TmRcd (R.Fld (indexOf b) (R.TmApp t t3 false) : Nil) /\ b
distApp _ _ = unsafeCrashWith $ "distApp"

distProj :: (R.Tm /\ C.Ty) -> Name -> Lowering (R.Tm /\ C.Ty)
distProj (t /\ a) l | isTopLike a = pure topRcd
distProj (t /\ C.TyRcd n a) l | n == l = (_  /\ a) <$> (rcdFld l t)
                              | otherwise = pure topRcd
distProj (t /\ C.TyAnd a b) l = do
    e1 /\ t1 <- distProj (t /\ a) l
    e2 /\ t2 <- distProj (t /\ b) l
    (_ /\ C.TyAnd t1 t2) <$> rcdCons e1 e2 
distProj _ _ = unsafeCrashWith $ "distProj"

subtype :: (R.Tm /\ C.Ty) -> C.Ty -> Lowering R.Tm
subtype (t /\ a) b |isTopLike b = pure $ R.TmRcd Nil
subtype ta@(t /\ a) b | Just (b1 /\ b2) <- split b = do
    t1 <- ta <: b1
    t2 <- ta <: b2
    unsplit (t1 /\ b1) b (t2 /\ b2)
subtype (t /\ a) b | a .=. b = do
    tr <- rcdFld (indexOf b) t
    pure $ R.TmRcd $ R.Fld (indexOf b) tr : Nil
subtype (t /\ C.TyArrow a1 a2 _) tb@(C.TyArrow b1 b2 _) = do
    x <- freshVarName
    t1 <- (R.TmVar x /\ b1) <: a1
    r1 <- projSubst t (indexOf tb) t1
    t2 <- (r1 /\ a2) <: b2
    pure $ R.TmRcd $ (R.Fld (indexOf tb) (R.TmAbs x t2 b1 b2 false false)) : Nil
subtype (t /\ C.TyAnd a1 a2) b = (t /\ a1) <: b <|> (t /\ a2) <: b
subtype (t /\ C.TyRcd l a) b = do
    r1 <- rcdFld (indexOf (C.TyRcd l a)) t
    e <- (r1 /\ a) <: b
    pure $ R.TmRcd $ (R.Fld (indexOf (C.TyRcd l a)) e : Nil)
subtype (_ /\ a) b = throwError $ "Lower.subtype: " <> show a <> " is not subtype of " <> show b

infix 4 subtype as <:

projSubst ::R.Tm -> Name -> R.Tm -> Lowering R.Tm
projSubst t0 l x = do
    t <- rcdFld l t0
    case t of
        R.TmAbs n b _ _ _ _ -> pure $ subst n x b
        _ ->  unsafeCrashWith $ "Lower.projSubst: " <> show t0 <+> l <+> show x

subst :: Name -> R.Tm -> R.Tm -> R.Tm
subst x e t@(R.TmUnary op t1) = R.TmUnary op (subst x e t1)
subst x e t@(R.TmBinary op t1 t2) = R.TmBinary op (subst x e t1) (subst x e t2)
subst x e t@(R.TmIf t1 t2 t3) = R.TmIf (subst x e t1) (subst x e t2) (subst x e t3)
subst x e t@(R.TmVar n) = if x == n then e else t
subst x e t@(R.TmApp l r b) = R.TmApp (subst x e l) (subst x e r) b
subst x e t@(R.TmAbs n b ta tr b1 b2) = if x == n then t else R.TmAbs n (subst x e b) ta tr b1 b2
subst x e t@(R.TmMerge t1 t2) = R.TmMerge (subst x e t1) (subst x e t2)
subst x e t@(R.TmRcd fs) = R.TmRcd $ map (\(R.Fld l z) -> R.Fld l (subst x e z)) fs
subst x e t@(R.TmRcdProj t1 l) = R.TmRcdProj (subst x e t1) l
subst _ _ t = t

unsplit :: (R.Tm /\ C.Ty) -> C.Ty -> (R.Tm /\ C.Ty) -> Lowering R.Tm 
unsplit (t1 /\ a) c (t2 /\ b) | isTopLike c = pure $ R.TmRcd Nil
unsplit (t1 /\ a) (C.TyAnd a' b') (t2 /\ b) | a === a' && b === b' = rcdCons t1 t2
unsplit (t1 /\ f1@(C.TyArrow a1 b1 _)) f@(C.TyArrow a b _) (t2 /\ f2@(C.TyArrow a2 b2 _)) = 
    case isTopLike b1, isTopLike b2 of
        false, false -> do
            x <- freshVarName
            let tx = R.TmVar x
            p1 <- projSubst t1 (indexOf f1) tx
            p2 <- projSubst t2 (indexOf f2) tx
            e <- unsplit (p1 /\ b1) b (p2 /\ b2)
            pure $ R.TmRcd $ R.Fld (indexOf f) (R.TmAbs x e a b false false) : Nil
        true, false -> do
            x <- freshVarName
            let tx = R.TmVar x
            p2 <- projSubst t2 (indexOf f2) tx
            e <- unsplit (R.TmRcd Nil /\ b1) b (p2 /\ b2)
            pure $ R.TmRcd $ R.Fld (indexOf f) (R.TmAbs x e a b false false) : Nil
        false, true -> do
            x <- freshVarName
            let tx = R.TmVar x
            p1 <- projSubst t1 (indexOf f1) tx
            e <- unsplit (p1 /\ b1) b (R.TmRcd Nil /\ b2)
            pure $ R.TmRcd $ R.Fld (indexOf f) (R.TmAbs x e a b false false) : Nil
        true, true -> pure $ R.TmRcd Nil
unsplit (t1 /\ f1@(C.TyRcd l1 a1)) f@(C.TyRcd l a) (t2 /\ f2@(C.TyRcd l2 a2)) = 
    case isTopLike a1, isTopLike a2 of
        false, false -> do
            p1 <- rcdFld (indexOf f1) t1
            p2 <- rcdFld (indexOf f2) t2
            e <- unsplit (p1 /\ a1) a (p2 /\ a2)
            pure $ R.TmRcd $ R.Fld (indexOf f) e : Nil
        true, false -> do
            p2 <- rcdFld (indexOf f2) t2
            e <- unsplit (R.TmRcd Nil /\ a1) a (p2 /\ a2)
            pure $ R.TmRcd $ R.Fld (indexOf f) e : Nil
        false, true -> do
            p1 <- rcdFld (indexOf f1) t1
            e <- unsplit (p1 /\ a1) a (R.TmRcd Nil /\ a2)
            pure $ R.TmRcd $ R.Fld (indexOf f) e : Nil
        true, true -> pure $ R.TmRcd Nil
unsplit (t1 /\ ty1) c (t2 /\ ty2) = unsafeCrashWith $ "Lower.unsplit"

topRcd :: R.Tm /\ C.Ty
topRcd = Tuple (R.TmRcd Nil) C.TyTop

rcdCons :: R.Tm -> R.Tm -> Lowering R.Tm
rcdCons (R.TmRcd fs1) (R.TmRcd fs2) = pure $ R.TmRcd (fs1 <> fs2)
rcdCons l r = throwError $ "cannot concat " <> show (l /\ r)

rcdFld :: Name -> R.Tm -> Lowering R.Tm
rcdFld l (R.TmRcd f) = go f
  where
    go Nil = throwError $ "not such field: " <> l
    go ((R.Fld n t):fs) 
      | n == l = pure t 
      | otherwise = go fs
rcdFld l t = throwError $ "cannot project" <> show (l /\ t)

-- todo remove test cases

test1 = C.TmMerge a b 
    where
        a = C.TmAbs "x" (C.TmBinary (Op.Arith Op.Add) (C.TmVar "x") (C.TmInt 1)) C.TyInt C.TyInt false  false
        b = C.TmAbs "x" (C.TmBool false) C.TyInt C.TyBool false false

test2 = C.TmApp test1 (C.TmInt 0) false

test3 = C.TmAnno test1 (C.TyArrow C.TyInt C.TyInt false)

test31 = C.TmAnno test1 (C.TyArrow C.TyInt (C.TyAnd C.TyBool C.TyInt) false)

test33 = C.TmMerge C.TmTop test1

test32 = C.TmAnno test33 (C.TyArrow C.TyInt C.TyInt false)

test4 = C.TmRcd "x" (C.TyAnd (C.TyArrow C.TyInt C.TyInt false) (C.TyArrow C.TyInt C.TyBool false)) test1

test36 = C.TmMerge test32 (C.TmAbs "x" (C.TmBool true) C.TyInt C.TyBool false false)
