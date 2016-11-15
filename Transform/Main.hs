import System.IO
import System.Environment
import Data.Aeson
import Data.Maybe
import Data.ByteString.Lazy hiding (putStrLn, unpack, pack, head)

import Transform.KModel
import Transform.KMTransform


{- Make hGetContents unambiguous -}
hGetContentsBS :: Handle -> IO ByteString
hGetContentsBS = Data.ByteString.Lazy.hGetContents

{- Main region -}
main = do
    args <- getArgs
    handle <- openFile (head args) ReadMode
    contents <- hGetContentsBS handle
    let x = (decode contents :: Maybe [Chapter]) in
        case x of
            Nothing   -> putStrLn "Invalid JSON..."
            _ -> print . tranformQuestionnaire $ fromJust x
