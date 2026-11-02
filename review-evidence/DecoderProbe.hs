import Control.Exception
import qualified Data.ByteString as BS
import Metron.Hash (decodeStored)

main :: IO ()
main = do
  let malformed = BS.pack [3, 0, 0, 1, 1, 0] -- scalar literal, numerator +1, denominator 0
  result <-
    try (evaluate (length (show (decodeStored malformed)))) ::
      IO (Either SomeException Int)
  print result
