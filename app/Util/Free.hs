-- Free(er) applicative functor derived from
-- https://arxiv.org/pdf/1403.0749.pdf
-- and
-- https://hackage.haskell.org/package/free-5.2/docs/Control-Applicative-Free.html

{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Util.Free where

import Util.Util (mapLeft, joinToString, fmt)
import Data.Void (Void, vacuous)
import Data.Text (Text, singleton, append)
import Control.Monad ((>=>))
import Data.Functor (($>))
import Data.Foldable (Foldable(..), traverse_)
import Data.Char (isAlpha, isDigit, digitToInt)
import Data.Bool (bool)
import Control.Arrow ((>>>))
import Control.Applicative.Free (Ap (..), runAp_)
import qualified Data.List (singleton)

-- Free(er) applicative functor, does not require "f" to be functorial!
-- data FreeA f a =
--     Pure a
--     | forall b. Ap (FreeA f (b -> a)) (f b)
-- deriving instance (Functor (FreeA f))

-- instance Applicative (FreeA f) where
--     pure = Pure
--     (<*>) :: FreeA f (c -> d) -> FreeA f c -> FreeA f d
--     Pure f <*> y = fmap f y
--     Ap x y <*> z = Ap (flip <$> x <*> z) y

-- runAp :: Applicative g => Natur f g -> FreeA f a -> g a
-- runAp _ (Pure x) = pure x
-- runAp u (Ap f x) = flip id <$> u x <*> runAp u f

-- Unit of the adjunction or something like that
-- one :: f a -> FreeA f a
-- one = Ap (Pure id)
one :: f a -> Ap f a
one x = Ap x (Pure id)

-- Free alternative functor
-- newtype Alt f a = Alt { alternatives :: [FreeA f a] }
--     deriving Functor

-- instance Applicative (Alt f) where
--   pure a = Alt [pure a]
--   (Alt xs) <*> ys = Alt (xs >>= alternatives . (`ap'` ys))
--     where
--       ap' :: FreeA f (a -> b) -> Alt f a -> Alt f b

--       Pure f `ap'` u      = fmap f u
--       (f `Ap` u) `ap'` v  = Alt [(_ <*> v) `Ap` u]

-- Base type constructor for parsers
-- "t" -- token type
-- "a" -- result type
data ParserOp t a where
    ZeroP :: ParserOp t Void
    MapErrorP :: (ExpectedTokens -> ExpectedTokens) -> Parser t a -> ParserOp t a
    TokenP :: (t -> Maybe a) -> ParserOp t a
    NotP :: Parser t () -> ParserOp t ()
    ChooseP :: [Parser t a] -> ParserOp t a
    FixP :: (Parser t a -> Parser t a) -> ParserOp t a
-- makeBaseFunctor ''ParserOp

-- data ParserOp t a =
--     ZeroP Text (Void -> a)
--     | TokenP t (t -> a)
--     | ChooseP (Parser t a) (Parser t a)
--     | FixP (Parser t a -> Parser t a)

zeroP :: Parser t Void
zeroP = Parser $ one ZeroP

mapErrorP :: (ExpectedTokens -> ExpectedTokens) -> Parser t a -> Parser t a
mapErrorP = ((Parser . one) .) . MapErrorP

tokenP :: (t -> Maybe a) -> Parser t a
tokenP = Parser . one . TokenP

notP :: Parser t () -> Parser t ()
notP = Parser . one . NotP

chooseP :: [Parser t a] -> Parser t a
chooseP = Parser . one . ChooseP

fixP :: (Parser t a -> Parser t a) -> Parser t a
fixP = Parser . one . FixP

type ExpectedTokens = [Text]

newtype Parser t a = Parser { unParser :: Ap (ParserOp t) a }
    deriving (Functor, Applicative)

type CompiledParser t a = [t] -> Either ExpectedTokens ([t], a)

showExpectedTokens :: ExpectedTokens -> Text
showExpectedTokens = joinToString >>> append "Expected: "

runParser :: Eq t => Parser t a -> [t] -> Either Text a
runParser = (mapLeft showExpectedTokens .) . execParser

execParser :: Eq t => Parser t a -> [t] -> Either ExpectedTokens a
execParser p = evalParser p >=> \case
    ([], r) -> Right r
    (_ : _, _) -> Left ["<eof>"]

evalParser :: Eq t => Parser t a -> CompiledParser t a
evalParser (Parser (Pure a)) = \ts -> Right (ts, a)
evalParser (Parser (Ap x k)) =
    let compiledK = evalParser (Parser k) in
    \ts -> do
    (tss, b) <- algebra1 x ts
    (tsss, f) <- compiledK tss
    pure (tsss, f b)

algebra1 :: Eq t => ParserOp t a -> CompiledParser t a
algebra1 ZeroP = const $ Left ["Zero error"]
algebra1 (MapErrorP newText p) =
    let compiledP1 = evalParser p in
    mapLeft newText . compiledP1
algebra1 (TokenP predicate) = \case
    [] -> Left ["Token match error"]
    (t : ts) -> maybe (Left ["Token match error"]) (Right . (ts,)) (predicate t)
algebra1 (NotP p) =
    let compiledP = evalParser p in
    \ts -> case compiledP ts of
        Left _ -> Right (ts, ())
        Right _ -> Left ["This should not have matched"]
algebra1 (ChooseP ps) =
    let compiledPs = map evalParser ps in go compiledPs
    where
        go :: Eq t => [CompiledParser t a] -> CompiledParser t a
        go [] = evalParser (vacuous zeroP)
        go (cp : cps) = \ts -> case cp ts of
            Left expected1 -> mapLeft (expected1 <>) (go cps ts)
            Right x -> Right x
algebra1 arg@(FixP pf) =
    evalParser (pf (Parser $ one arg))

showParser :: Parser t a -> Text
showParser = joinToString . runAp_ (Data.List.singleton . natur) . unParser
    where
        natur :: ParserOp t a -> Text
        natur ZeroP = "zero"
        natur (MapErrorP _ p) = fmt "MapErrorP(_, %)" [showParser p]
        natur (TokenP _) = "TokenP(_)"
        natur (NotP p) = fmt "NotP(%, %)" [showParser p]
        natur (ChooseP ps) = fmt "ChooseP(%)" [joinToString $ map showParser ps]
        natur (FixP f) = fmt "FixP(%)" [showParser $ f (vacuous $ failP "<recurse>")]

-- Combinators
-- instance Alternative (Parser t) where
--     empty = vacuous zeroP
--     (<|>) (Parser x) (Parser y) = Parser $ runAp foo x
--         where
--             foo :: ParserOp t a -> Ap (ParserOp t) a
--             foo ZeroP = one ZeroP
--             foo (ChooseP ps) = one (ChooseP $ ps ++ [y])
--             foo (MapErrorP f p) = _

-- simplify :: Parser t a -> Parser t a

failP :: Text -> Parser t Void
failP err = mapErrorP (const [err]) zeroP

tryP :: Parser t () -> Parser t ()
tryP = chooseP . (: [pure ()])

annotateErrorP :: Text -> Parser t a -> Parser t a
annotateErrorP err = mapErrorP (const [err])
-- annotateErrorP err = (`chooseP` (vacuous $ failP err))

tokenP2 :: Text -> (t -> Maybe a) -> Parser t a
tokenP2 err = annotateErrorP err . tokenP

-- tokenP2 :: Text -> (t -> Maybe a) -> FreeA (ParserOp t) a
-- tokenP2 err = annotateErrorP err . tokenP

tokenPBool :: (t -> Bool) -> Parser t t
tokenPBool predicate = tokenP \t -> bool Nothing (Just t) (predicate t)

tokenP2Bool :: Text -> (t -> Bool) -> Parser t t
tokenP2Bool err = annotateErrorP err . tokenPBool

tokenOneP :: Eq t => t -> Parser t t
tokenOneP = tokenPBool . (==)

tokenOneP2 :: Eq t => Text -> t -> Parser t t
tokenOneP2 err = tokenP2Bool err . (==)

someFromBoundMany :: Parser t [a] -> Parser t a -> Parser t [a]
someFromBoundMany boundMany p = do
    x <- p
    xs <- boundMany
    pure (x : xs)

manyP :: Parser t a -> Parser t [a]
manyP p = fixP \self ->
    let boundSome = someFromBoundMany self p
    in chooseP [boundSome, pure []]

someP :: Parser t a -> Parser t [a]
someP p = someFromBoundMany (manyP p) p

oneOfP :: [Parser t a] -> Parser t a
oneOfP = chooseP

alphaP :: Parser Char Char
alphaP = tokenP2Bool "<alpha>" isAlpha

digitP :: Parser Char Char
digitP = tokenP2Bool "<digit>" isDigit

keywordP :: String -> Parser Char String
keywordP kw = traverse_ (\c -> tokenP2Bool (singleton c) (== c)) kw $> kw

keywordP' :: String -> Parser Char ()
keywordP' kw = keywordP kw $> ()

intP :: Parser Char Word
intP = foldl' (+) 0 . zipWith (*) powers . reverse <$> wordDigits
    where
        wordDigits = someP (fromIntegral . digitToInt <$> digitP)
        powers = iterate (*10) 1