{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Util.Util where

import Data.Functor.Const (Const (..))
import Data.Text (Text, append, cons, empty, pack, unpack)
import Effectful (Eff, type (:>), raise, liftIO, IOE)
import Effectful.Error.Static (Error, HasCallStack, throwError, CallStack, prettyCallStack, runError)
import Data.Maybe (fromMaybe)
import Control.Arrow ((>>>))
import Control.Exception (throwIO)
import Control.Monad (when, (>=>))
import Data.Functor (($>))
import Data.Functor.Foldable (Recursive, Corecursive, Base, embed, project)
import Control.Lens (Iso', iso)
import Effectful.Reader.Static (Reader, runReader)
import Effectful.State.Static.Local (State, get)

fromTrue :: Maybe Bool -> Bool
fromTrue = fromMaybe False

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

bindLeft :: (a -> Either b c) -> Either a c -> Either b c
bindLeft k = either k Right

joinToString :: [Text] -> Text
joinToString = joinToString' ", "

joinToString' :: Text -> [Text] -> Text
-- joinToString' = intercalate
joinToString' _ [] = empty
joinToString' _ [x] = x
joinToString' sep (x:xs) = fmt "%%%" [x, sep, joinToString' sep xs]

fmt :: String -> [Text] -> Text
fmt [] (_:_) = error "too many arguments"
fmt [] [] = empty
fmt ('%':_) [] = error "not enough arguments"
fmt ('%':xs) (arg:args) = arg `append` fmt xs args
fmt (x:xs) args = x `cons` fmt xs args

runTextError :: IOE :> es => Eff (Error Text ': es) a -> Eff es a
runTextError = runError >=> either
    (showCallStack >>> unpack >>> userError >>> throwIO >>> liftIO)
    pure

throwText :: (HasCallStack, Error Text :> es) => Text -> Eff es a
throwText = throwError

fromJustText :: (HasCallStack, Error Text :> es) => Maybe a -> Eff es a
fromJustText Nothing = throwText "aa"
fromJustText (Just x) = pure x

eitherToError :: (HasCallStack, Error Text :> es) => Either Text b -> Eff es b
eitherToError = either throwText pure

weakenReader :: Eff (Reader r ': es) a -> Eff (State r ': es) a
weakenReader act = get >>= ((`runReader` act) >>> raise)
-- weakenReader = s (s (const (=<<)) ((raise . ) . flip runReader)) (const get)

maybeToEff :: Applicative f => f a -> Maybe a -> f a
maybeToEff def = maybe def pure

checkEqual :: (HasCallStack, Error Text :> es, Eq a) => a -> a -> Text -> Eff es a
checkEqual x y msg = when (x /= y) (throwText msg) $> x

showCallStack :: (CallStack, Text) -> Text
showCallStack (cs, msg) = fmt "% at\n%" [msg, pack $ prettyCallStack cs]

constO :: Const () a
constO = Const ()

type TextChain = [Text]

textChainToText :: [Text] -> Text
textChainToText = joinToString' empty

unreachable :: HasCallStack => a
unreachable = error "unreachable"

unreachableError :: (HasCallStack, Error Text :> es) => Eff es a
unreachableError = throwText "unreachable"

-- Combines `genericIndex` and `atMay`
genericAtMay :: Integral i => [a] -> i -> Maybe a
genericAtMay [] _ = Nothing
genericAtMay (x:_) 0 = Just x
genericAtMay (_:xs) index = genericAtMay xs (index - 1)

wordFindIndex :: forall a. (a -> Bool) -> [a] -> Maybe Word
wordFindIndex predicate = go 0
    where
        go :: Word -> [a] -> Maybe Word
        go _ [] = Nothing
        go i (x : _) | predicate x = Just i
        go i (_ : xs) = go (i + 1) xs

unsingletonExact :: [a] -> Either Text a
unsingletonExact [] = Left "not enough values"
unsingletonExact [x] = Right x
unsingletonExact (_:_:_) = Left "too many values"

type Natur f g = forall x. f x -> g x

baseIso :: (Recursive a, Corecursive a, Base a a ~ b) => Iso' a b
baseIso = iso project embed

-- mapAccum :: ((b, c) -> a -> f (b, c)) -> (b, c) -> [a] -> f c
-- mapAccum f start list = snd <$> traverse f (pure start) list