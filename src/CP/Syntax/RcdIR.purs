module Language.CP.Syntax.RcdIR where

import Prelude

import Data.List (List(..), intercalate, (:))
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Common (BinOp, Name, UnOp, Label, brackets, parens)
import Language.CP.Syntax.Core (Ty)
import Language.CP.Util ((<+>))
import Partial.Unsafe (unsafeCrashWith)

-- Record Fields --

data Fld a = Fld Label a

instance Show a => Show (Fld a) where
  show (Fld l ty) = l <> ": " <> show ty

derive instance Eq a => Eq (Fld a)

-- Types --

{- data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyUnit
        | TyTop
        | TyBot
        | TyArrow Ty Ty
        | TyAnd Ty Ty
        | TyOr Ty Ty
        | TyVar Name
        | TyForall Name Ty Ty
        | TyRef Ty
        | TyArray Ty
        | TyRcd (List (Fld Ty))

instance Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyUnit   = "()"
  show TyTop    = "Top"
  show TyBot    = "Bot"
  show (TyArrow t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (TyAnd t1 t2) = parens $ show t1 <+> "&" <+> show t2
  show (TyOr t1 t2) = parens $ show t1 <+> "|" <+> show t2
  show (TyVar a) = a
  show (TyForall a td t) = parens $
    "forall" <+> a <+> "*" <+> show td <> "." <+> show t
  show (TyRef t) = parens $ "Ref" <+> show t
  show (TyArray t) = brackets $ show t
  show (TyRcd flds) = "{" <> intercalate "," (map show flds) <> "}"

derive instance Eq Ty -}

-- Terms --

data Tm = TmInt Int
        | TmDouble Number
        | TmString String
        | TmBool Boolean
        | TmUnit
        | TmUndefined
        | TmUnary UnOp Tm
        | TmBinary BinOp Tm Tm
        | TmIf Tm Tm Tm
        | TmVar Name
        | TmApp Tm Tm Boolean
        | TmAbs Name Tm Ty Ty Boolean Boolean
        | TmFix Name Tm Ty
        | TmMerge Tm Tm
        | TmSwitch Tm Name (List (Ty /\ Tm))
        | TmTApp Tm Ty
        | TmTAbs Name Ty Tm Ty Boolean
        | TmRef Tm
        | TmDeref Tm
        | TmAssign Tm Tm
        | TmToString Tm
        | TmArray Ty (Array Tm)
        -- TODO: record literals, projection, concatenation
        | TmRcd (List (Fld Tm))
        | TmRcdProj Tm Label
        | TmRcdCons Tm Tm
        | TmDef Name Tm Tm
        | TmMain Tm

instance Show Tm where
  show (TmInt i)    = show i
  show (TmDouble n) = show n
  show (TmString s) = show s
  show (TmBool b)   = show b
  show TmUnit       = "()"
  show TmUndefined  = "undefined"
  show (TmUnary op e) = show op <> show e
  show (TmBinary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (TmIf e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (TmVar x) = x
  show (TmApp e1 e2 _coercive) = parens $ show e1 <+> show e2
  show (TmAbs x e _targ _tret _refined _trait) = parens $
    "λ" <> x <> "." <+> show e
  show (TmFix x e _t) = parens $ "fix" <+> x <> "." <+> show e
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmSwitch e x cases) = parens $
    "switch" <+> show e <+> "as" <+> x <+>
    intercalate " " (cases <#> \(t /\ e') -> "case" <+> show t <+> "->" <+> show e')
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs a _td e _t _refined) = parens $ "Λ" <> a <> "." <+> show e
  show (TmRef e) = parens $ "ref" <+> show e
  show (TmDeref e) = "!" <> show e
  show (TmAssign e1 e2) = parens $ show e1 <+> ":=" <+> show e2
  show (TmToString e) = parens $ "toString" <+> show e
  show (TmArray _t arr) = brackets $ intercalate "; " (show <$> arr)
  show (TmRcd flds) = "{" <> intercalate "," (map show flds) <> "}"
  show (TmRcdProj r l) = show r <> "." <> l
  show (TmRcdCons l r) = show l <> "++" <> show r
  show (TmDef x e1 e2) = x <+> "=" <+> show e1 <> ";\n" <> show e2
  show (TmMain e) = show e
