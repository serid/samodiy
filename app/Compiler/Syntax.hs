{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TemplateHaskell #-}

module Compiler.Syntax where
import Util.Free (Parser, manyP, chooseP, alphaP, digitP, keywordP, oneOfP, execParser, ExpectedTokens, intP, tokenP2, tokenOneP, tokenOneP2, tryP, tokenPBool, someP, failP)
import Data.Text (Text, pack)
import Data.Functor (($>), (<&>), void)
import Control.Lens (makePrisms, (^?))
import Data.Void (vacuous)

-- Tokenizer

data Token =
    TClass
    | TFun
    | TForall
    | TMatch
    | TEnd
    | TParenL
    | TParenR
    | TComma
    | TBar
    | TInt !Word
    | TIdent !Text
    | TString !Text
    deriving (Show, Eq)
makePrisms ''Token

tokenize :: String -> Either ExpectedTokens [Token]
tokenize = execParser tokenizer

tokenizer :: Parser Char [Token]
tokenizer = manyP (waybeWhitespace *> parsers)
    where
        waybeWhitespace = do
            tryP $ void $ tokenOneP ' '
            tryP $ void $ tokenOneP '\n'
            pure ()

        parsers = oneOfP [
                keywordP "class" $> TClass,
                keywordP "fun" $> TFun,
                keywordP "forall" $> TForall,
                keywordP "match" $> TMatch,
                keywordP "end" $> TEnd,
                keywordP "(" $> TParenL,
                keywordP ")" $> TParenR,
                keywordP "," $> TComma,
                keywordP "|" $> TBar,
                intP <&> TInt,
                identT <&> TIdent,
                stringT <&> TString
            ]

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

-- Parser

data ClassDef = ClassDef {
    _className :: !Text,
    _classMethods :: ![MethodDef]
} deriving (Show, Eq)

data MethodDef = MethodDef {
    _methodName :: !Text,
    _methodParams :: ![(Text, AstExpr)],
    _methodBody :: ![Stmt]
} deriving (Show, Eq)

data AstExpr =
    AstInt !Word
    | AstString !Text
    deriving (Show, Eq)

data Stmt =
    StmtExpr !AstExpr
    | StmtLet
    deriving (Show, Eq)

classP :: Parser Token ClassDef
classP = do
    tokenOneP TClass
    name <- identP
    methods <- manyP methodP
    tokenOneP TEnd
    pure $ ClassDef name methods

classP1 :: Parser Char ClassDef
classP1 = do
    keywordP "class "
    name <- identT
    keywordP " end"
    pure $ ClassDef name []

methodP :: Parser Token MethodDef
methodP = do
    tokenOneP TFun
    name <- identP
    
    tokenOneP TParenL
    let params = []
    tokenOneP TParenR

    body <- manyP stmtP
    tokenOneP TEnd
    pure $ MethodDef name params body

stmtP :: Parser Token Stmt
stmtP = do
    StmtExpr <$> exprP

exprP :: Parser Token AstExpr
exprP = do
    vacuous $ failP "todo"