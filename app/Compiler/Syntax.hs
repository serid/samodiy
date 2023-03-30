{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

module Compiler.Syntax where
import Util.Free (Parser, manyP, chooseP, alphaP, digitP, keywordP, oneOfP, execParser, ExpectedTokens, intP, tokenP2, tokenOneP, tokenOneP2, tokenPBool, someP, tokenP)
import Data.Text (Text, pack)
import Data.Functor (($>), (<&>))
import Control.Lens (makePrisms, (^?))
import Tyck.Model (NamefulExpr, NamefulStmt, GStmtF (StmtExprF), GExpr (..))
import Util.Util (constO)
import Tyck.Builtins (Builtin(..))
import Control.Monad ((<=<))

-- Tokenizer

data Token =
    TClass
    | TFun
    | TForall
    | TMatch
    | TEnd
    | TLet
    | TArrow
    | TFatArrow
    | TComma
    | TEqual
    | TBar
    | TParenL
    | TParenR
    -- | TBraceL
    -- | TBraceR
    | TInt !Word
    | TIdent !Text
    | TString !Text
    deriving (Show, Eq)
makePrisms ''Token

tokenize :: String -> Either ExpectedTokens [Token]
tokenize = execParser tokenizer

tokenizer :: Parser Char [Token]
tokenizer = manyP (waybeWhitespace *> parsers) <* waybeWhitespace
    where
        waybeWhitespace = manyP $ chooseP [tokenOneP ' ', tokenOneP '\n']

        -- You can use keywords in english (latin) or finnish (latin, hangul)
        parsers = oneOfP [
                keywordChoiceP ["class", "luokka", "루오카"] $> TClass,
                keywordChoiceP ["fun", "fun", "와운"] $> TFun,
                keywordChoiceP ["for", "kai", "카이"] $> TForall,
                keywordChoiceP ["match", "sovittaa", "소위타"] $> TMatch,
                keywordChoiceP ["end", "loppu", "로푸"] $> TEnd,
                keywordChoiceP ["let", "antaa", "안타"] $> TLet,
                keywordP "->" $> TArrow,
                keywordP "=>" $> TFatArrow,
                keywordP "," $> TComma,
                keywordP "=" $> TEqual,
                keywordP "|" $> TBar,
                keywordP "(" $> TParenL,
                keywordP ")" $> TParenR,
                -- keywordP "{" $> TBraceL,
                -- keywordP "}" $> TBraceR,
                intP <&> TInt,
                identT <&> TIdent,
                stringT <&> TString
            ]
        
        keywordChoiceP = chooseP . fmap keywordP

identT :: Parser Char Text
identT = pack <$> someP (chooseP [alphaP, digitP])

identP :: Parser Token Text
identP = tokenP2 "ident" (^? _TIdent)

stringT :: Parser Char Text
stringT = do
    tokenOneP2 "quote" '\"'
    str <- manyP (tokenPBool (/= '\"'))
    tokenOneP2 "quote" '\"'
    pure $ pack str

execSP :: Parser Token a -> String -> Either ExpectedTokens a
execSP p = execParser p <=< tokenize

-- Parser

newtype ModuleDef = ModuleDef {
    _items :: [ToplevelDef]
} deriving (Show, Eq)

data ToplevelDef =
    ToplevelClass !ClassDef
    | ToplevelLet !Text !NamefulExpr !NamefulExpr
    deriving (Show, Eq)

data ClassDef = ClassDef {
    _className :: !Text,
    _classMethods :: ![FunDef]
} deriving (Show, Eq)

data FunDef = FunDef {
    _funName :: !Text,
    _funParams :: ![(Text, NamefulExpr)],
    _funBody :: !NamefulExpr
} deriving (Show, Eq)

classP1 :: Parser Char ClassDef
classP1 = do
    keywordP "class "
    name <- identT
    keywordP " end"
    pure $ ClassDef name []

moduleP :: Parser Token ModuleDef
moduleP = do
    ModuleDef <$> manyP (chooseP [classP <&> ToplevelClass, letP{-, funP <&> ToplevelFun-}])

classP :: Parser Token ClassDef
classP = do
    tokenOneP TClass
    name <- identP
    -- methods <- manyP methodP
    tokenOneP TEnd
    pure $ ClassDef name [] {-methods-}

letP :: Parser Token ToplevelDef
letP = do
    tokenOneP TLet
    name <- identP
    tokenOneP TEqual
    ini <- exprP
    pure $ ToplevelLet name (Hole constO) ini

funP :: Parser Token FunDef
funP = do
    tokenOneP TFun
    name <- identP
    
    tokenOneP TParenL
    let params = []
    tokenOneP TParenR

    body <- exprP
    -- body <- manyP stmtP
    tokenOneP TEnd
    pure $ FunDef name params body

lamP :: Parser Token NamefulExpr
lamP = do
    tokenOneP TFun
    tokenOneP TParenL
    let params = []
    tokenOneP TParenR
    tokenOneP TFatArrow
    expr <- exprP
    tokenOneP TEnd
    pure $ Lam constO params expr

stmtP :: Parser Token NamefulStmt
stmtP = do
    StmtExprF <$> exprP

exprP :: Parser Token NamefulExpr
exprP = chooseP [
        tokenP (^? _TInt) <&> Builtin constO . BInt . fromIntegral,
        lamP
    ]