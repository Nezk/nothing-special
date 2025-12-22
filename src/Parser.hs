{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Parser (parseRDefs, runSC) where

import Control.Monad (void)

import Data.Bifunctor (first)

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language (emptyDef)

import qualified Text.Parsec.Token as T

import Syntax
import Wellscoped

-- todo: rewrite the parser

-- Parsing --------------------------------------------------------------------

type Parser = Parsec String ()

langDef :: T.LanguageDef ()
langDef = emptyDef
    { T.commentStart    = "{-",
      T.commentEnd      = "-}",
      T.commentLine     = "--",
      T.identStart      = letter <|> char '_',
      T.identLetter     = alphaNum <|> char '_' <|> char '\'',
      T.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~→λ×ℕ≔",
      T.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~→λ×ℕ≔",
      T.reservedOpNames = [ "->", "→", ":=", "≔", "\\", "λ", ".", ",",
                            "*", "×", ":", "=", "@", ".1", ".2", "?" ],
      T.reservedNames   = [ "let", "in", "U", "Nat", "ℕ", "Z", "S",
                            "ind", "J", "refl", "contra" ] }

lexer      = T.makeTokenParser langDef
identifier = T.identifier lexer
reserved   = T.reserved   lexer
reservedOp = T.reservedOp lexer
parens     = T.parens     lexer
braces     = T.braces     lexer
whiteSpace = T.whiteSpace lexer
integer    = fromIntegral <$> T.integer lexer

pTerm :: Parser Raw
pTerm = try pLet
    <|> try pLam
    <|> try pDep
    <|> do
        t <- pExpr
        option t $ do
            reservedOp "->" <|> reservedOp "→"
            RFun t <$> pTerm

pExpr :: Parser Raw
pExpr = buildExpressionParser table pEq
  where table = [[Infix ((reservedOp "*"  <|> reservedOp "×") >> return RTimes) AssocRight]]

pEq :: Parser Raw
pEq = do
    l <- pSpine
    option l $ do
        reservedOp "="
        r <- pSpine
        reservedOp "@"
        ty <- pSpine
        return $ REql ty l r

pSpine :: Parser Raw
pSpine = do
    hd <- pProj
    args <- many pProj
    return $ foldl RApp hd args

pProj :: Parser Raw
pProj = pAtom >>= go
  where go t = choice
          [reservedOp ".1" >> go (RFst t),
           reservedOp ".2" >> go (RSnd t),
           return t]

pAtom :: Parser Raw
pAtom = choice
        [reserved "U"      >> RU <$> integer,
        (reserved "Nat"   <|> reserved "ℕ") >> return RNat,
         reserved "Z"      >> return RZero,
         reserved "S"      >> RSucc <$> pProj,
         reserved "refl"   >> return RRefl,
         reserved "contra" >> RContra <$> pProj,
         reserved "ind"    >> RInd <$> braces integer <*> pProj <*> pProj <*> pProj <*> pProj,
         reserved "J"      >> RJ <$> pProj <*> pProj <*> braces integer <*> pProj <*> pProj <*> pProj <*> pProj,
         pHole,
         pVar,
         parens pPair]

pHole :: Parser Raw
pHole = do
    reservedOp "?"
    name <- option "" $ try $ do
        n <- identifier
        notFollowedBy (reservedOp ":")
        return n
    return $ RHole name

pVar :: Parser Raw
pVar = try $ do
    v <- identifier
    notFollowedBy (reservedOp ":")
    return $ RVar v

pPair :: Parser Raw
pPair = sepBy1 pTerm (reservedOp ",") >>= \case
        [e]      -> return e
        (x : xs) -> return $ foldr RPair (last xs) (x : init xs)
        []       -> unexpected "Empty parens"

pLet :: Parser Raw
pLet = do
    reserved "let"
    x <- identifier
    ty <- optionMaybe $ do reservedOp ":"; pTerm
    reservedOp ":=" <|> reservedOp "≔"
    val <- pTerm
    reserved "in"
    RLet x ty val <$> pTerm

pLam :: Parser Raw
pLam = do
    void $ reservedOp "\\" <|> reservedOp "λ"
    xs <- many1 identifier
    reservedOp "."
    body <- pTerm
    return $ foldr RLam body xs

pDep :: Parser Raw
pDep = do
    tel <- many1 pTele
    choice [do reservedOp "->" <|> reservedOp "→"
               body <- pTerm
               return $ foldr (\(x, t) b -> RPi x t b) body (concat tel),
            do reservedOp "*" <|> reservedOp "×"
               body <- pTerm
               return $ foldr (\(x, t) b -> RSigma x t b) body (concat tel)]

pTele :: Parser [(String, Raw)]
pTele = parens $ do
    xs <- many1 identifier
    reservedOp ":"
    ty <- pTerm
    return $ map (, ty) xs

-- Definitions parsing --------------------------------------------------------

pDef :: Parser (String, Raw, Maybe Raw)
pDef = do
    n <- identifier
    reservedOp ":"
    t <- pTerm
    v <- optionMaybe $ do
        reservedOp ":=" <|> reservedOp "≔"
        pTerm
    return (n, t, v)

pDefs :: Parser [(String, Raw, Maybe Raw)]
pDefs = whiteSpace >> many pDef <* eof

parseRDefs :: String -> Either String [(String, Raw, Maybe Raw)]
parseRDefs = first show . parse pDefs ""
