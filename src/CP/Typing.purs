module Language.CP.Typing where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Error.Class (throwError)
import Control.Monad.State (gets, modify_)
import Data.Array (all, elem, head, notElem, null, unzip)
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr, lookup, traverse_)
import Data.List (List(..), filter, last, singleton, sort, (:), length)
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (Checking, Pos(..), TypeError(..), Typing, addSort, addTmBind, addTyBind, fromState, localPos, lookupTmBind, lookupTyBind, runTyping, throwTypeError)
import Language.CP.Desugar (deMP, desugar)
import Language.CP.Subtyping (isTopLike, (<:), (===))
import Language.CP.Syntax.Common (BinOp(..), CompOp(..), Label, Name, UnOp(..))
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.Transform (transform, transform', transformTyDef)
import Language.CP.TypeDiff (tyDiff)
import Language.CP.Util (foldl1, foldr1, unsafeFromJust, (<+>))

-- TODO: you may try to write source subtyping directly
sub :: S.Ty -> S.Ty -> Typing Boolean
sub t1 t2 = do
  t1' <- transform t1
  t2' <- transform t2
  pure $ t1' <: t2'

aeq :: S.Ty -> S.Ty -> Typing Boolean
aeq t1 t2 = do
  t1' <- transform t1
  t2' <- transform t2
  pure $ t1' === t2'

infer :: S.Tm -> Typing (C.Tm /\ S.Ty)
infer (S.TmInt i)    = pure $ C.TmInt i /\ S.TyInt
infer (S.TmDouble d) = pure $ C.TmDouble d /\ S.TyDouble
infer (S.TmString s) = pure $ C.TmString s /\ S.TyString
infer (S.TmBool b)   = pure $ C.TmBool b /\ S.TyBool
infer S.TmUnit       = pure $ C.TmUnit /\ S.TyUnit
infer S.TmUndefined  = pure $ C.TmUndefined /\ S.TyBot
-- Int is always prioritized over Double: e.g. -(1.0,2) = -2
infer (S.TmUnary Neg e) = do
  e' /\ t <- infer e
  let core cty sty = C.TmUnary Neg (C.TmAnno e' cty) /\ sty
  tSubInt <- t `sub` S.TyInt
  tSubDouble <- t `sub` S.TyDouble
  if tSubInt then pure $ core C.TyInt S.TyInt
  else if tSubDouble then pure $ core C.TyDouble S.TyDouble
  else throwTypeError $ "Neg is not defined for" <+> show t
infer (S.TmUnary Len e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Len e' /\ S.TyInt
  case t of S.TyArray _ -> pure core
            _ -> throwTypeError $ "Len is not defined for" <+> show t
infer (S.TmUnary Sqrt e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Sqrt e' /\ S.TyDouble
  case t of S.TyDouble -> pure core
            _ -> throwTypeError $ "Sqrt is not defined for" <+> show t
infer (S.TmBinary (Arith op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty sty = C.TmBinary (Arith op) (C.TmAnno e1' ty) (C.TmAnno e2' ty) /\ sty
  s1 <- sub t1 S.TyInt
  s2 <- sub t2 S.TyInt
  if s1 && s2 then pure $ core C.TyInt S.TyInt
  else do
    s1' <- sub t1 S.TyDouble
    s2' <- sub t2 S.TyDouble
    if s1' && s2' then pure $ core C.TyDouble S.TyDouble
    else throwTypeError $
      "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Comp op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty = C.TmBinary (Comp op) (C.TmAnno e1' ty)
                                     (C.TmAnno e2' ty) /\ S.TyBool
  p1 <- (&&) <$> sub t1 S.TyInt <*> sub t2 S.TyInt
  if p1 then pure $ core C.TyInt
  else do
    p2 <- (&&) <$> sub t1 S.TyDouble <*> sub t2 S.TyDouble
    if p2 then pure $ core C.TyDouble
    else do
      p3 <- (&&) <$> sub t1 S.TyString <*> sub t2 S.TyString
      if p3 then pure $ core C.TyString
      else do
        p4 <- (&&) <$> sub t1 S.TyBool <*> sub t2 S.TyBool
        if p4 then pure $ core C.TyBool
        else case t1, t2, isEqlOrNeq op of
          S.TyRef _, S.TyRef _, true -> pure $ C.TmBinary (Comp op) e1' e2' /\ S.TyBool
          _, _, _ -> throwTypeError $
            "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where isEqlOrNeq :: CompOp -> Boolean
        isEqlOrNeq Eql = true
        isEqlOrNeq Neq = true
        isEqlOrNeq _ = false
infer (S.TmBinary (Logic op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core = C.TmBinary (Logic op) (C.TmAnno e1' C.TyBool)
                                   (C.TmAnno e2' C.TyBool) /\ S.TyBool
  p <- (&&) <$> sub t1 S.TyBool <*> sub t2 S.TyBool
  if p then pure core
  else throwTypeError $
    "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Append e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  p1 <- (&&) <$> sub t1 S.TyString <*> sub t2 S.TyString
  if p1 then
    pure $ C.TmBinary Append (C.TmAnno e1' C.TyString)
                             (C.TmAnno e2' C.TyString) /\ S.TyString
  else case t1, t2 of
    S.TyArray t1', S.TyArray t2' -> do
      let core el er sty = C.TmBinary Append el er /\ sty
      p2 <- aeq t1' t2'
      if p2 then pure $ core e1' e2' t1
      else do
        s1 <- sub t2' t1'
        tr1 <- transform t1
        if s1 then pure $ core e1' (C.TmAnno e2' tr1) t1
        else do
          s2 <- sub t1' t2'
          tr2 <- transform t2
          if s2 then pure $ core (C.TmAnno e1' tr2) e2' t2
          else throwTypeError $
            "Append expected two arrays of equivalent types or subtypes," <+>
            "but got" <+> show t1' <+> "and" <+> show t2'
    _, _ -> throwTypeError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Index e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let te t1 t2 = throwTypeError $ "Index is not defined between" <+> show t1 <+> "and" <+> show t2
  case t1 of 
    S.TyArray t1' -> do
      p <- sub t2 S.TyInt 
      if p then pure $ C.TmBinary Index e1' (C.TmAnno e2' C.TyInt) /\ t1'
      else te t1 t2
    _ -> te t1 t2
infer (S.TmIf e1 e2 e3) = do
  e1' /\ t1 <- infer e1
  s1 <- sub t1 S.TyBool
  if s1 then do
    e2' /\ t2 <- infer e2
    e3' /\ t3 <- infer e3
    let core et ef sty = C.TmIf (C.TmAnno e1' C.TyBool) et ef /\ sty
    e1 <- aeq t2 t3
    if e1 then pure $ core e2' e3' t2
    else do
      s2 <- sub t3 t2 
      tr2 <- transform t2
      if s2 then pure $ core e2' (C.TmAnno e3' tr2) t2
      else do
        s3 <- sub t2 t3
        tr3 <- transform t3
        if s3 then pure $ core (C.TmAnno e2' tr3) e3' t3
        else throwTypeError $
          "if-branches expected two equivalent types or subtypes, but got" <+>
          show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
infer (S.TmVar x) = (C.TmVar x /\ _) <$> lookupTmBind x
infer (S.TmApp e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of 
    S.TyArrow targ tret -> do
      p1 <- aeq t2 targ
      if p1 then pure $ C.TmApp e1' e2' false /\ tret
      else do
        labels <- collectOpt <$> transform targ
        p2 <- (\t2' targ' -> t2' `andOpt` labels <: targ') <$> transform t2 <*> transform targ
        if length labels > 0 && p2 then
          let merge acc l = C.TmMerge acc (C.TmRcd l C.TyUnit C.TmUnit) 
              e2'' = foldl merge e2' labels 
          in pure $ C.TmApp e1' e2'' false /\ tret
        else throwTypeError "TODO distApp for S.Ty"
    _ -> throwTypeError "TODO distApp for S.Ty"
        -- (C.TmApp e1' e2' true /\ _) <$> distApp t1 (Left t2) -- TODO distApp for S.Ty
  where collectOpt :: C.Ty -> List Label  -- TODO: collect optional labels in a safer way
        collectOpt (C.TyAnd t1 t2) = collectOpt t1 <> collectOpt t2
        collectOpt (C.TyRcd l (C.TyOr _ C.TyUnit)) = singleton l
        collectOpt _ = Nil
        andOpt = foldl (\acc l -> C.TyAnd acc (C.TyRcd l C.TyUnit))
infer (S.TmAbs (S.TmParam x (Just targ) : Nil) e) = do
  targ' <- transform targ
  e' /\ tret <- addTmBind x targ $ infer e
  tret' <- transform tret
  pure $ C.TmAbs x e' targ' tret' false false /\ S.TyArrow targ tret
infer (S.TmAbs (S.TmParam x Nothing : Nil) _) = throwTypeError $
  "lambda parameter" <+> show x <+> "should be annotated with a type"
infer (S.TmAbs (S.WildCard _ : Nil) _) = throwTypeError $
  "record wildcards should only occur in traits with interfaces implemented"
infer (S.TmFix x e t) = do
  t' <- transform t
  e' /\ t'' <- addTmBind x t $ infer e
  p <- sub t'' t
  if p then pure $ C.TmFix x e' t' /\ t'' else throwTypeError $
    "fix body expected a subtype of the annotated type, but got " <+> show t''
infer (S.TmAnno e ta) = do
  e' /\ t <- infer e
  ta' <- transform ta
  p <- sub t ta
  if p then pure $ C.TmAnno e' ta' /\ ta else throwTypeError $
    "annotated" <+> show ta <+> "is not a supertype of inferred" <+> show t
infer (S.TmMerge S.Neutral e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1, t2 of
    S.TyTop, _ -> pure $ e2' /\ t2
    _, S.TyTop -> pure $ e1' /\ t1
    S.TyTrait ti1 to1, S.TyTrait ti2 to2 -> do
      to1' <- transform to1
      to2' <- transform to2
      disjoint to1' to2'
      let ti = case ti1, ti2 of Nothing, Just i2 -> Just i2
                                Just i1, Nothing -> Just i1
                                Just i1, Just i2 -> Just $ S.TyAnd i1 i2
                                Nothing, Nothing -> Nothing
      trait "$self" (C.TmMerge (appToSelf e1') (appToSelf e2')) ti (S.TyAnd to1 to2)
    _, _ -> do
      t1' <- transform t1
      t2' <- transform t2
      disjoint t1' t2'
      let res = case mkRcd (S.TyAnd t1 t2) of 
                  Nil /\ st -> fromMaybe S.TyTop st
                  sr /\ st -> S.TyAnd (S.TyRcd sr) (fromMaybe S.TyTop st)
      pure $ C.TmMerge e1' e2' /\ res
  where appToSelf e = C.TmApp e (C.TmVar "$self") true
infer (S.TmMerge S.Leftist e1 e2) =
  infer $ S.TmMerge S.Neutral e1 (S.TmDiff e2 e1)
infer (S.TmMerge S.Rightist e1 e2) =
  infer $ S.TmMerge S.Neutral (S.TmDiff e1 e2) e2
-- TODO: make sure case types are disjoint
infer (S.TmSwitch e alias cases) = do
  tte <- for cases \(ti /\ ei) -> do
    ti' <- transform ti
    ei' /\ to <- maybe identity (\x -> addTmBind x ti) alias $ infer ei
    pure $ to /\ ti' /\ ei'
  m <- maximal (fst <$> tte)
  case m of
    Just to -> do
      let cases' = snd <$> tte
          union = foldl1 C.TyOr (fst <$> cases')
      e' /\ t <- infer e
      t' <- transform t
      to' <- transform to
      if t' <: union then
        let switch = C.TmSwitch e' (fromMaybe "$alias" alias) cases' in
        pure $ C.TmAnno switch to' /\ to
      else throwTypeError $ "switch expression expected a subtype of" <+> show union
                         <> ", but got" <+> show t
    Nothing -> throwTypeError $ "switch cases have different types"
  where maximal :: List S.Ty -> Typing (Maybe S.Ty)
        maximal Nil = pure $ Just S.TyBot
        maximal (t : ts) = do
          mt <- maximal ts
          case mt of
            Just t' -> do
              p1 <- sub t t'
              if p1 then pure $ Just t'
              else do
                p2 <- sub t'  t 
                if p2 then  pure $ Just t
                else pure Nothing
            Nothing -> pure Nothing
infer (S.TmRcd Nil) = pure $ C.TmTop /\ S.TyRcd Nil
infer (S.TmRcd (S.RcdField _ l Nil (Left e) : Nil)) = do
  e' /\ t <- infer e
  t' <- transform t
  pure $ C.TmRcd l t' e' /\ S.TyRcd (S.RcdTy l t false : Nil)
infer (S.TmPrj e l) = do
  e' /\ t <- infer e
  t' <- transform t
  let r = case t' of C.TyRec _ _ -> C.TmUnfold t' e' -- /\ C.unfold t'
                     _ -> e' -- /\ t'
  case selectLabel' t l of
    Just t'' -> pure $ C.TmPrj r l /\ t''
    _ -> throwTypeError $ "label" <+> show l <+> "is absent in" <+> show t
{- -- TODO distApp for S.Type
infer (S.TmTApp e ta) = do
  e' /\ tf <- infer e
  ta' <- transform ta
  t <- distApp tf (Right ta')
  pure $ C.TmTApp e' ta' /\ t 
-}
infer (S.TmTAbs ((a /\ Just td) : Nil) e) = do
  td' <- transform td
  e' /\ t <- addTyBind a td $ infer e
  t' <- transform t
  pure $ C.TmTAbs a td' e' t' false /\ S.TyForall ((a /\ Just td) : Nil) t
infer (S.TmLet x Nil Nil e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- addTmBind x t1 $ infer e2
  t1' <- transform t1
  t2' <- transform t2
  pure $ letIn x e1' t1' e2' t2' /\ t2
infer (S.TmLetrec x Nil Nil t e1 e2) = do
  e1' /\ t1 <- inferRec x e1 t
  e2' /\ t2 <- addTmBind x t1 $ infer e2
  t1' <- transform t1
  t2' <- transform t2
  pure $ letIn x (C.TmFix x e1' t1') t1' e2' t2' /\ t2
-- TODO: find a more efficient algorithm
infer (S.TmOpen e1 e2) = do
  e1' /\ t1 <- infer e1
  t1' <- transform t1
  let r /\ tr = case t1' of C.TyRec _ _ -> C.TmUnfold t1' e1' /\ C.unfold t1'
                            _ -> e1' /\ t1'
      b = foldr (\l s -> (l /\ unsafeFromJust (selectLabel' t1 l)) : s)
                Nil (collectLabels tr)
  e2' /\ t2 <- foldr (uncurry addTmBind) (infer e2) b
  t2' <- transform t2
  b' <- traverse (\(n /\ t) -> (\z -> n /\ z) <$> transform t) b
  -- `open` is the only construct that elaborates to a lazy definition
  let open (l /\ t) e = letIn l (C.TmPrj (C.TmVar opened) l) t e t2'
  pure $ letIn opened r tr (foldr open e2' b') t2' /\ t2
  where opened = "$open"
infer (S.TmUpdate rcd fields) = do
  rcd' /\ t <- infer rcd
  fields' <- for fields \(l /\ e) -> do
    e' /\ t' <- infer e
    pure $ l /\ (e' /\ t')
  let t' = S.TyRcd (map (\(l /\ (e' /\ t')) -> S.RcdTy l t' false) fields')
  cfs <- for fields' \(l /\ (e' /\ t')) -> do
    ct' <- transform t'
    pure $ C.TmRcd l ct' e'
  let ct' = foldr rcdTy C.TyTop cfs
  ct <- transform t
  if ct <: ct' then do
    d <- tyDiff t t' >>= transform
    let merge = if isTopLike d then identity else C.TmMerge (C.TmAnno rcd' d)
        updating = foldr1 C.TmMerge cfs
    pure $ merge updating /\ t
  else throwTypeError $ "cannot safely update the record" <+> show rcd
  where rcdTy :: C.Tm -> C.Ty -> C.Ty
        rcdTy (C.TmRcd l t _) s = C.TyAnd (C.TyRcd l t) s
        rcdTy _ s = s
{- TODO: modify the following code similarly
infer (S.TmTrait (Just (self /\ Just t)) (Just sig) me1 ne2) = do
  t' <- transform t
  sig'' /\ sig' <- transform' sig
  e2 <- inferFromSig sig' ne2
  ret /\ tret <- case me1 of
    Just e1 -> do
      -- self may be used in e1 (e.g. trait [self:T] inherits f self => ...)
      -- this self has nothing to do with that self in the super-trait
      e1' /\ t1 <- addTmBind self t' $ infer e1
      case t1 of
        C.TyArrow ti to true -> do
          if t' <: ti then do
            e2' /\ t2 <-
              addTmBind self t' $ addTmBind "super" to $ infer e2
            let to' = override to e2
            disjoint to' t2
            let tret = C.TyAnd to' t2
                ret = letIn "super" (C.TmApp e1' (C.TmVar self) true) to
                      (C.TmMerge (C.TmAnno (C.TmVar "super") to') e2') tret
            pure $ ret /\ tret
          else throwTypeError $ "self-type" <+> show t <+>
            "is not a subtype of inherited self-type" <+> show ti
        _ -> throwTypeError $ "expected to inherit a trait, but got" <+> show t1
    Nothing -> do
      e2' /\ t2 <- addTmBind self t' $ infer e2
      pure $ e2' /\ t2
  if tret <: sig'' then pure $ trait self ret t' tret
  else throwTypeError $ "the trait does not implement" <+> show sig
  where
    -- TODO: inference is not complete
    inferFromSig :: S.Ty -> S.Tm -> Typing S.Tm
    inferFromSig rs@(S.TyAnd _ _) e = inferFromSig (S.TyRcd $ combineRcd rs) e
    inferFromSig s@(S.TyRec _ ty) e = S.TmFold s <$> inferFromSig ty e
    inferFromSig s (S.TmPos p e) = S.TmPos p <$> inferFromSig s e
    inferFromSig s (S.TmOpen e1 e2) = S.TmOpen e1 <$> inferFromSig s e2
    inferFromSig s (S.TmMerge bias e1 e2) =
      S.TmMerge bias <$> inferFromSig s e1 <*> inferFromSig s e2
    inferFromSig (S.TyRcd xs) r@(S.TmRcd (S.RcdField o l Nil (Left e) : Nil)) =
      case last $ filterRcd (_ == l) xs of
        Just (S.RcdTy _ ty _) -> do
          e' <- inferFromSig ty e
          pure $ S.TmRcd (singleton (S.RcdField o l Nil (Left e')))
        _ -> pure r
    inferFromSig (S.TyRcd xs)
        (S.TmRcd (S.DefaultPattern pat@(S.MethodPattern _ label _ _) : Nil)) =
      desugar <<< S.TmRcd <$> for (filterRcd (_ `notElem` patterns label) xs)
        \(S.RcdTy l ty _) -> do
          let params /\ ty' = paramsAndInnerTy ty
          e <- inferFromSig ty' (desugar (deMP pat))
          pure $ S.RcdField false l params (Left e)
      where patterns :: Label -> Array Label
            patterns l = patternsFromRcd (S.TmMerge S.Neutral (fromMaybe S.TmUnit me1) ne2) l
            patternsFromRcd :: S.Tm -> Label -> Array Label
            patternsFromRcd (S.TmPos _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmOpen _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmMerge _ e1 e2) l =
              patternsFromRcd e1 l <> patternsFromRcd e2 l
            patternsFromRcd (S.TmRcd (S.RcdField _ l' _ (Left e) : Nil)) l =
              if innerLabel e == l then [l'] else []
            patternsFromRcd _ _ = []
            innerLabel :: S.Tm -> Label
            innerLabel (S.TmPos _ e) = innerLabel e
            innerLabel (S.TmOpen _ e) = innerLabel e
            innerLabel (S.TmAbs _ e) = innerLabel e
            innerLabel (S.TmTrait _ _ _ e) = innerLabel e
            innerLabel (S.TmRcd (S.RcdField _ l _ _ : Nil)) = l
            innerLabel _ = "$nothing"
            paramsAndInnerTy :: S.Ty -> S.TmParamList /\ S.Ty
            paramsAndInnerTy (S.TyArrow targ tret) =
              let params /\ ty = paramsAndInnerTy tret in
              (S.TmParam "_" (Just targ) : params) /\ ty
            paramsAndInnerTy ty = Nil /\ ty
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.TmParam x mt : Nil) e) =
      S.TmAbs (singleton (S.TmParam x (mt <|> Just targ))) <$> inferFromSig tret e
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.WildCard defaults : Nil) e) =
      let fields = combineRcd targ in
      if defaults `matchOptional` fields then do
        e' <- inferFromSig tret e
        pure $ S.TmAbs (singleton (S.TmParam wildcardName (Just targ))) (open fields e')
      else throwTypeError $ "default arguments do not match optional parameters"
      where wildcardName = "$wildcard"
            wildcardVar = S.TmVar wildcardName
            open fields body = foldr letFieldIn body fields
            letFieldIn (S.RcdTy l tl opt) acc =
              if opt then let default = unsafeFromJust $ lookup l defaults
                              cases = (tl /\ S.TmVar l) : (S.TyUnit /\ default) : Nil
                              switch = S.TmSwitch (S.TmPrj wildcardVar l) (Just l) cases in
                          S.TmLet l Nil Nil switch acc
              else S.TmLet l Nil Nil (S.TmPrj wildcardVar l) acc
    inferFromSig (S.TyTrait ti to) (S.TmTrait (Just (self' /\ mt)) sig' e1 e2) = do
      let t' = fromMaybe (fromMaybe S.TyTop ti) mt
      e1' <- traverse (inferFromSig to) e1
      e2' <- inferFromSig to e2
      pure $ S.TmTrait (Just (self' /\ Just t')) sig' e1' e2'
    inferFromSig (S.TyForall ((a /\ td) : as) ty) (S.TmTAbs ((a' /\ td') : Nil) e) =
      S.TmTAbs (singleton (a' /\ (td' <|> td))) <$> inferFromSig ty' e
      where ty' = (if as == Nil then identity else S.TyForall as)
                  (S.tySubst a (S.TyVar a') ty)
    inferFromSig _ e = pure e
    combineRcd :: S.Ty -> S.RcdTyList
    combineRcd (S.TyAnd (S.TyRcd xs) (S.TyRcd ys)) = xs <> ys
    combineRcd (S.TyAnd l (S.TyRcd ys)) = combineRcd l <> ys
    combineRcd (S.TyAnd (S.TyRcd xs) r) = xs <> combineRcd r
    combineRcd (S.TyAnd l r) = combineRcd l <> combineRcd r
    combineRcd (S.TyRcd rcd) = rcd
    combineRcd _ = Nil
    filterRcd :: (Label -> Boolean) -> S.RcdTyList -> S.RcdTyList
    filterRcd f = filter \(S.RcdTy l _ _) -> f l
    override :: C.Ty -> S.Tm -> C.Ty
    override ty e = let ls = selectOverride e in
      if null ls then ty else removeOverride ty ls
      where selectOverride :: S.Tm -> Array Label
            selectOverride (S.TmPos _ e0) = selectOverride e0
            selectOverride (S.TmOpen _ e0) = selectOverride e0
            selectOverride (S.TmMerge _ e1 e2) = selectOverride e1 <> selectOverride e2
            -- TODO: only override the inner field if it's a method pattern
            selectOverride (S.TmRcd (S.RcdField true l _ _ : Nil)) = [l]
            selectOverride _ = []
            -- TODO: make sure every field overrides some field in super-trait
            removeOverride :: C.Ty -> Array Label -> C.Ty
            removeOverride (C.TyAnd t1 t2) ls =
              let t1' = removeOverride t1 ls
                  t2' = removeOverride t2 ls in
              case t1', t2' of
                C.TyTop, C.TyTop -> C.TyTop
                C.TyTop, _       -> t2'
                _,       C.TyTop -> t1'
                _,       _       -> C.TyAnd t1' t2'
            removeOverride (C.TyRcd l _) ls | l `elem` ls = C.TyTop
            removeOverride typ _ = typ
    matchOptional :: S.DefaultFields -> S.RcdTyList -> Boolean
    matchOptional def rcd = sort labels == sort labels' -- identical up to permutation
      where labels = fst <$> def
            labels' = foldr (\(S.RcdTy l _ opt) s -> if opt then l : s else s) Nil rcd
infer (S.TmTrait (Just (self /\ Nothing)) sig e1 e2) =
  infer $ S.TmTrait (Just (self /\ Just S.TyTop)) sig e1 e2
infer (S.TmNew e) = do
  e' /\ t <- infer e
  case t of
    C.TyArrow ti to true ->
      if to <: ti then
        pure $ C.TmFix "$self" (C.TmApp e' (C.TmVar "$self") true) to /\ to
      else throwTypeError $ "input type is not a supertype of output type in" <+>
                            "Trait<" <+> show ti <+> "=>" <+> show to <+> ">"
    _ -> throwTypeError $ "new expected a trait, but got" <+> show t
infer (S.TmForward e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of
    C.TyArrow ti to true ->
      if t2 <: ti then pure $ C.TmApp e1' e2' true /\ to
      else throwTypeError $ "expected to forward to a subtype of" <+> show ti <>
                            ", but got" <+> show t2
    _ -> throwTypeError $ "expected to forward from a trait, but got" <+> show t1
infer (S.TmExclude e te) = do
  e' /\ t <- infer e
  te' <- transform te
  -- `check` helps to make sure `l` was present in `e` before exclusion,
  -- since the field removal `e \ l` desugars to `e \\ {l : Bot}`
  let check = case te' of C.TyRcd l C.TyBot -> checkLabel l
                          _ -> const $ pure unit
  case t of
    C.TyArrow ti to true -> do
      check to
      d <- tyDiff to te'
      let t' = C.TyArrow ti d true
      pure $ C.TmAnno e' t' /\ t'
    _ -> do
      check t
      d <- tyDiff t te'
      pure $ C.TmAnno e' d /\ d
  where checkLabel :: Label -> C.Ty -> Typing Unit
        checkLabel l (C.TyAnd t1 t2) = checkLabel l t1 <|> checkLabel l t2
        checkLabel l (C.TyRcd l' _) | l == l' = pure unit
        checkLabel l _ = throwTypeError $ "label" <+> show l <+> "is absent in" <+> show e
infer (S.TmRemoval e l) = do
  infer $ S.TmExclude e (S.TyRcd (singleton (S.RcdTy l S.TyBot false)))
infer (S.TmDiff e1 e2) = do
  e1' /\ t1 <- infer e1
  _ /\ t2 <- infer e2
  case t1, t2 of
    C.TyArrow ti to1 true, C.TyArrow _ to2 true -> do
      d <- tyDiff to1 to2
      pure $ trait "$self" (C.TmAnno (C.TmApp e1' (C.TmVar "$self") true) d) ti d
    _, _ -> do
      d <- tyDiff t1 t2
      pure $ C.TmAnno e1' d /\ d
infer (S.TmRename e old new) = do
  _ /\ t <- infer e
  case t of
    -- TODO: compiled code does not terminate because (e1^e2) is no more lazy
    C.TyArrow ti _ true ->
      case selectLabel ti old of
        Just tl -> do
          -- e [old <- new] := trait [self] =>
          --   let super = self [new <- old] in
          --   (e ^ super) [old <- new]
          let super = S.TmRename (S.TmVar "$self") new old
              body = S.TmRename (S.TmForward e super) old new
          tself <- C.TyAnd (C.TyRcd new tl) <$> tyDiff ti (C.TyRcd old C.TyBot)
          ret /\ tret <- addTmBind "$self" tself $ infer body
          pure $ trait "$self" ret tself tret
        Nothing -> do
          -- e [old <- new] := trait [self] => (e ^ self) [old <- new]
          let body = (S.TmRename (S.TmForward e (S.TmVar "$self")) old new)
          ret /\ tret <- addTmBind "$self" ti $ infer body
          pure $ trait "$self" ret ti tret
    _ ->
      -- e [old <- new] := e \ old , {new = e.old}
      infer $ S.TmMerge S.Neutral (S.TmRemoval e old)
        (S.TmRcd (singleton (S.RcdField false new Nil (Left (S.TmPrj e old)))))
infer (S.TmFold t e) = do
  t' <- transformTyRec t
  e' /\ t'' <- infer e
  if t'' <: C.unfold t' then pure $ C.TmFold t' e' /\ t'
  else throwTypeError $ "cannot fold" <+> show e <+> "to" <+> show t
infer (S.TmUnfold t e) = do
  t' <- transformTyRec t
  e' /\ t'' <- infer e
  if t'' <: t' then pure $ C.TmUnfold t' e' /\ C.unfold t'
  else throwTypeError $ "cannot unfold" <+> show e <+> "to" <+> show t
infer (S.TmRef e) = do
  e' /\ t <- infer e
  pure $ C.TmRef e' /\ C.TyRef t
infer (S.TmDeref e) = do
  e' /\ t <- infer e
  case t of C.TyRef t' -> pure $ C.TmDeref e' /\ t'
            _ -> throwTypeError $ "cannot dereference" <+> show t
infer (S.TmAssign e1 e2) = do
  e1' /\ t1 <- infer e1
  case t1 of C.TyRef t1' -> do e2' /\ t2 <- infer e2
                               if t2 <: t1' then pure $ C.TmAssign e1' e2' /\ C.TyUnit
                               else throwTypeError $ "assigned type" <+> show t2 <+>
                                                     "is not a subtype of" <+> show t1'
             _ -> throwTypeError $ "assignment expected a reference type, but got" <+> show t1
infer (S.TmSeq e1 e2) = do
  e1' /\ t1 <- infer e1
  case t1 of C.TyUnit -> do e2' /\ t2 <- infer e2
                            pure $ letIn "_" e1' t1 e2' t2 /\ t2
             _ -> throwTypeError $ "sequencing expected a unit type, but got" <+> show t1
infer (S.TmToString e) = do
  e' /\ t <- infer e
  if t == C.TyInt || t == C.TyDouble || t == C.TyString || t == C.TyBool
  then pure $ C.TmToString e' /\ C.TyString
  else throwTypeError $ "cannot show" <+> show t
infer (S.TmArray arr) = do
  if null arr then
    pure $ C.TmArray C.TyBot [] /\ C.TyArray C.TyBot
  else do
    ets <- traverse infer arr
    let es /\ ts = unzip ets
        t = unsafeFromJust $ head ts
    if all (_ === t) ts then pure $ C.TmArray t es /\ C.TyArray t
    else throwTypeError $ "elements of an array should all have the same type" <>
                          ", but got" <+> show (S.TmArray arr)
infer (S.TmDoc doc) = localPos f $ infer doc
  where f (Pos p e _) = Pos p e true
        f UnknownPos = UnknownPos
-- TODO: save original terms instead of desugared ones
infer (S.TmPos p e) = localPos f $ infer e
  where f (Pos _ _ inDoc) = Pos p e inDoc
        f UnknownPos = Pos p e false
-}
infer e = throwTypeError $ "expected a desugared term, but got" <+> show e

inferRec :: Name -> S.Tm -> S.Ty -> Typing (C.Tm /\ S.Ty)
inferRec x e t = do
  e' /\ t1 <- addTmBind x t $ infer e
  isSub <- t1 `sub` t
  if isSub then do
    isAeq <- t1 `aeq` t
    t' <- transform t
    pure $ (if isAeq then e' else C.TmAnno e' t') /\ t
  else throwTypeError $
    "annotated" <+> show t <+> "is not a supertype of inferred" <+> show t1

checkDef :: S.Def -> Checking Unit
checkDef (S.TyDef def a sorts params t) = do
  forbidDup <- gets (_.forbidDup)
  aliases <- gets (_.tyAliases)
  if forbidDup && isJust (lookup a aliases) then
    throwError $ TypeError ("type" <+> show a <+> "has already been defined") UnknownPos
  else case def of
    S.TypeAlias -> do
      ctx <- gets fromState
      case runTyping (addSorts $ addTyBinds $ transformTyDef t) ctx of
        Left err -> throwError err
        Right t' -> modify_ \st -> st { tyAliases = (a /\ sig t') : st.tyAliases }
    S.Interface -> do
      ctx <- gets fromState
      case runTyping (addSorts $ addTyBinds $ addTyBind a S.TyTop $ transformTyDef t) ctx of
        Left err -> throwError err
        Right t' -> modify_ \st -> st { tyAliases = (a /\ sig (S.TyRec a t')) : st.tyAliases }
                                                -- TODO: S.TyRec a (sig t')
    S.InterfaceExtends super -> do
      checkDef $ S.TyDef S.Interface (a <> "_") sorts params (S.tySubst a (S.TyVar (a <> "_")) t)
      let self = S.TyVar (a <> "_") # withSorts # withParams
      checkDef $ S.TyDef S.TypeAlias a sorts params (S.TyAnd super self)
  where
    dualSorts :: List (Name /\ Name)
    dualSorts = sorts <#> \sort -> sort /\ (sort <> "_")
    addSorts :: forall a. Typing a -> Typing a
    addSorts typing = foldr (uncurry addSort) typing dualSorts
    addTyBinds :: forall a. Typing a -> Typing a
    addTyBinds typing = foldr (flip addTyBind S.TyTop) typing params
    sig :: S.Ty -> S.Ty
    sig t' = foldr (uncurry S.TySig) (foldr S.TyAbs t' params) dualSorts    
    withSorts :: S.Ty -> S.Ty
    withSorts t' = let sort = S.TyVar >>> flip S.TySort Nothing in
                   foldl (S.TyApp >>> (sort >>> _)) t' sorts
    withParams :: S.Ty -> S.Ty
    withParams t' = foldl (S.TyApp >>> (S.TyVar >>> _)) t' params
checkDef (S.TmDef x Nil Nil mt e) = do
  forbidDup <- gets (_.forbidDup)
  bindings <- gets (_.tmBindings)
  if forbidDup && isJust (lookup x bindings) then
    throwError $ TypeError ("term" <+> show x <+> "has already been defined") UnknownPos
  else do
    ctx <- gets fromState
    let typing = case mt of Just t -> inferRec x e t
                            Nothing -> infer e
    case runTyping typing ctx of
      Left err -> throwError err
      Right (e' /\ t') ->
        case runTyping (transform t') ctx of
          Left err -> throwError err
          Right t'' ->
            let e1 = if isJust mt then C.TmFix x e' t'' else e'
                f e2 = C.TmDef x e1 e2 in
            modify_ \st -> st { tmBindings = (x /\ t' /\ f) : st.tmBindings }
checkDef d = throwError $ TypeError ("expected a desugared def, but got" <+> show d) UnknownPos

checkProg :: S.Prog -> Checking (C.Tm /\ S.Ty)
checkProg (S.Prog defs e) = do
  traverse_ checkDef defs
  ctx <- gets fromState
  case runTyping (infer e) ctx of
    Left err -> throwError err
    Right (e' /\ t) -> pure $ C.TmMain e' /\ t

distApp :: C.Ty -> Either C.Ty C.Ty -> Typing C.Ty
distApp (C.TyArrow targ tret _) (Left t) | t <: targ = pure tret
                                         | otherwise = throwTypeError $
  "expected the argument type to be a subtype of the parameter type, but got" <+>
  show t <+> "and" <+> show targ
distApp (C.TyForall a td t) (Right ta) = disjoint ta td $> C.tySubst a ta t
distApp (C.TyAnd t1 t2) t = do
  t1' <- distApp t1 t
  t2' <- distApp t2 t
  pure $ C.TyAnd t1' t2'
distApp t _ = throwTypeError $ "expected an applicable type, but got" <+> show t

disjoint :: C.Ty -> C.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (C.TyArrow _ t1 _) (C.TyArrow _ t2 _) = disjoint t1 t2
disjoint (C.TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (C.TyAnd t2 t3) = disjoint (C.TyAnd t2 t3) t1
disjoint (C.TyRcd l1 t1) (C.TyRcd l2 t2) | l1 == l2  = disjoint t1 t2
                                         | otherwise = pure unit
disjoint (C.TyVar a) (C.TyVar b) =
  disjointVar a (C.TyVar b) <|> disjointVar b (C.TyVar a)
disjoint (C.TyVar a) t = disjointVar a t
disjoint t (C.TyVar a) = disjointVar a t
disjoint (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) =
  disjointTyBind a1 t1 a2 t2 (C.TyAnd td1 td2)
disjoint (C.TyRec a1 t1) (C.TyRec a2 t2) = disjointTyBind a1 t1 a2 t2 C.TyBot
disjoint t1 t2 | t1 /= t2  = pure unit
               | otherwise = throwTypeError $
  "expected two disjoint types, but got" <+> show t1 <+> "and" <+> show t2

disjointVar :: Name -> C.Ty -> Typing Unit
disjointVar a t = do
  mt' <- lookupTyBind a
  case mt' of
    Just t' -> do
      t'' <- transform t'
      if t'' <: t then pure unit else throwTypeError $
        "type variable" <+> show a <+> "is not disjoint from" <+> show t
    Nothing -> throwTypeError $ "type variable" <+> show a <+> "is undefined"

-- TODO: fix disjointTyBind
disjointTyBind :: Name -> C.Ty -> Name -> C.Ty -> C.Ty -> Typing Unit
disjointTyBind _ _ _ _ _ = pure unit
-- disjointTyBind a1 t1 a2 t2 td = addTyBind freshName td $
--   disjoint (C.tySubst a1 freshVar t1) (C.tySubst a2 freshVar t2)
--   where freshName = a1 <> " or " <> a2
--         freshVar = C.TyVar freshName

letIn :: Name -> C.Tm -> C.Ty -> C.Tm -> C.Ty -> C.Tm
letIn x e1 t1 e2 t2 = C.TmApp (C.TmAbs x e2 t1 t2 false false) e1 false

trait :: Name -> C.Tm -> Maybe S.Ty -> S.Ty -> Typing (C.Tm /\ S.Ty)
trait x e targ tret = do
  let t = case targ of Just t -> t
                       Nothing -> S.TyTop
  targ' <- transform t
  tret' <- transform tret
  pure $ C.TmAbs x e targ' tret' false (not $ isTopLike targ') /\ S.TyTrait targ tret
  -- skip traits whose self-type is top-like

collectLabels :: C.Ty -> Set.Set Label
collectLabels (C.TyAnd t1 t2) = Set.union (collectLabels t1) (collectLabels t2)
collectLabels (C.TyRcd l _) = Set.singleton l
collectLabels _ = Set.empty

selectLabel' :: S.Ty -> Label -> Maybe S.Ty
selectLabel' (S.TyAnd t1 t2) l =
  case selectLabel' t1 l, selectLabel' t2 l of
    Just t1', Just t2' -> Just (S.TyAnd t1' t2')
    Just t1', Nothing  -> Just t1'
    Nothing,  Just t2' -> Just t2'
    Nothing,  Nothing  -> Nothing
selectLabel' (S.TyRcd rs) l = lookup l (map (\(S.RcdTy l' t _) -> l' /\ t) rs)
selectLabel' _ _ = Nothing

selectLabel :: C.Ty -> Label -> Maybe C.Ty
selectLabel (C.TyAnd t1 t2) l =
  case selectLabel t1 l, selectLabel t2 l of
    Just t1', Just t2' -> Just (C.TyAnd t1' t2')
    Just t1', Nothing  -> Just t1'
    Nothing,  Just t2' -> Just t2'
    Nothing,  Nothing  -> Nothing
selectLabel (C.TyRcd l' t) l | l == l' = Just t
selectLabel _ _ = Nothing

-- reconstruct multi field records
mkRcd :: S.Ty -> S.RcdTyList /\ Maybe S.Ty
mkRcd (S.TyRcd rs) = rs /\ Nothing
mkRcd (S.TyAnd l r) = 
  let lr /\ lt = mkRcd l
      rr /\ rt = mkRcd r
  in (lr <> rr) /\ (S.TyAnd <$> lt <*> rt)
mkRcd t = Nil /\ Just t
