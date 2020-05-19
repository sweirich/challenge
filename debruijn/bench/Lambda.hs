-- | This file is adapted from Lennart Auggustsson's "Lambda Calculus Cooked Four Ways"

module Lambda(LC(..), freeTyVars, freeTmVars, freeTyVarsE, Id(..)) where

import Data.Functor (($>))
import Data.List(union, (\\))
import Data.Char(isAlphaNum)
import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text, (<+>), parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.ReadP
import Data.Map (Map)
import qualified Data.Map


data Ty v = IntTy | Ty v :-> Ty v | VarTy v | AllTy v (Ty v)
   deriving (Eq)
data LC v = VarE v | LamE v (Ty v) (LC v) | AppE (LC v) (LC v)
          | TyLam v (LC v) | TyApp (LC v) (Ty v)
   deriving (Eq)

freeTyVars :: (Eq v) => Ty v -> [v]
freeTyVars IntTy = []
freeTyVars (t1 :-> t2) = freeTyVars t1 `union` freeTyVars t2
freeTyVars (VarTy v) = [v]
freeTyVars (AllTy v t) = freeTyVars t \\ [v]

freeTmVars :: (Eq v) => LC v -> [v]
freeTmVars (VarE v) = [v]
freeTmVars (LamE v _ e) = freeTmVars e \\ [v]
freeTmVars (AppE f a) = freeTmVars f `union` freeTmVars a
freeTmVars (TyLam _ e) = freeTmVars e
freeTmVars (TyApp e _) = freeTmVars e

freeTyVarsE :: (Eq v) => LC v -> [v]
freeTyVarsE (VarE v) = []
freeTyVarsE (LamE v t e) = freeTyVarsE e `union` freeTyVars t
freeTyVarsE (AppE f a) = freeTyVarsE f `union` freeTyVarsE a
freeTyVarsE (TyLam v e) = freeTyVarsE e \\ [v]
freeTyVarsE (TyApp e t) = freeTyVarsE e `union` freeTyVars t


instance (Read v) => Read (LC v) where
     readsPrec _ = readP_to_S pLC

-- A ReadP parser for $\lambda$-expressions.

pTy, pTyVar :: (Read v) => ReadP (Ty v)
pTy = pTyVar +++
      (string "Int" $> IntTy) +++
      (do _ <- sstring "all"
          v <- pVar 
          _ <- schar '.'
          AllTy v <$> pTy)  +++
      (do _ <- schar '('
          t1 <- pTy
          _ <- sstring ":->"
          t2 <- pTy
          _ <- schar ')'
          return $ t1 :-> t2)
pTyVar = VarTy <$> pVar

pLC, pLCAtom, pLCVar, pLCLam, pLCApp, pLCTyLam :: (Read v) => ReadP (LC v)
pLC = pLCLam +++ pLCTyLam +++ pLCApp +++ pLCLet
pLCVar = VarE <$> pVar
pLCLam = do
    _ <- schar '\\'
    v <- pVar
    _ <- schar ':'
    t <- pTy 
    _ <- schar '.'
    LamE v t <$> pLC
pLCTyLam = do
    _ <- schar '\\'
    v <- pVar
    _ <- schar '.'
    TyLam v <$> pLC
pLCApp = do
    es <- many1 pLCAtom
    return $ foldl1 AppE es
pLCAtom = pLCVar +++ (do _ <- char '('; e <- pLC; _ <- char ')'; return e)

-- To make expressions a little easier to read we also allow let expression
-- as a syntactic sugar for $\lambda$ and application.

pLCLet :: (Read v) => ReadP (LC v)
pLCLet = do
    let lcLet (x,t,e) b = AppE (LamE x t b) e
        pDef = do
          v <- pVar
          _ <- schar ':'
          t <- pTy
          _ <- schar '='
          e <- pLC
          return (v, t, e)
    _ <- sstring "let"
    bs <- sepBy pDef (char ';')
    _ <- sstring "in"
    e <- pLC
    return $ foldr lcLet e bs

schar :: Char -> ReadP Char
schar c = do skipSpaces; char c

sstring :: String -> ReadP String
sstring c = do skipSpaces; string c

pVar :: (Read v) => ReadP v
pVar = do skipSpaces; readS_to_P (readsPrec 9)


-- Pretty print $\lambda$-expressions when shown.

instance (Show v) => Show (LC v) where
    show = renderStyle style . ppLC 0

ppLC :: (Show v) => Int -> LC v -> Doc
ppLC _ (VarE v) = text $ show v
ppLC p (LamE v t e) = pparens (p>0) $ text ("\\" ++ show v ++ ".") PP.<> ppLC 0 e
ppLC p (AppE f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a
ppLC p (TyLam v e) = pparens (p>0) $ text ("/\\" ++ show v ++ ".") PP.<> ppLC 0 e
ppLC p (TyApp e t) = pparens (p>1) $ ppLC 1 e <+> ppTy 2 t

ppTy :: (Show v) => Int -> Ty v -> Doc
ppTy _ IntTy = text "Int"
ppTy p (VarTy v) = text $ show v
ppTy p (t1 :-> t2) = pparens (p >1) $ ppTy 2 t1 <+> ppTy 1 t2
ppTy p (AllTy v t) = pparens (p>0) $ text "all" <+> text (show v ++ ".") PP.<> ppTy 0 t

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

-- The Id type of identifiers.

newtype Id = Id String
    deriving (Eq, Ord)

-- Identifiers print and parse without any adornment.

instance Show Id where
     show (Id i) = i

instance Read Id where
    readsPrec _ s =
        case span isAlphaNum s of
        ("", _) -> []
        (i, s') -> [(Id i, s')]
