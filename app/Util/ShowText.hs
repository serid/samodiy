module Util.ShowText where

import Data.Text (Text, pack, unpack)

class ShowText a where
    showText :: a -> Text

instance ShowText () where
    showText = showTextFromShow

instance ShowText Int where
    showText = showTextFromShow

instance ShowText Word where
    showText = showTextFromShow

instance ShowText Text where
    showText = id

showTextFromShow :: Show a => (a -> Text)
showTextFromShow = pack . show

showFromShowText :: ShowText a => (a -> String)
showFromShowText = unpack . showText