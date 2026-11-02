-- | Stable numerical source identities and their canonical encoding.
module Metron.Numerical.Identity (
  SourceId (..),
  Origin (..),
  originId,
) where

import Crypto.Hash.SHA256 qualified as SHA256 (hashlazy)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (length)
import Data.ByteString.Builder (Builder, byteString, toLazyByteString, word8)
import Data.Text (Text)
import Metron.Core (Hash (..))
import Metron.Encode (sint, text, varint)

-- | A content-derived identity shared across evaluations.
newtype SourceId = SourceId ByteString
  deriving stock (Eq, Ord, Show)

-- | The lexical or labelled source of an input (design §3.2.4).
data Origin
  = -- | A sample: enclosing definition, path to the node and component
    Declared Hash [Int] Int
  | -- | the same, written with a @#label@: one unknown wherever the label appears
    Tagged Text Int
  deriving stock (Eq, Ord, Show)

-- | An input source identity from its encoding.
sourceId :: Builder -> SourceId
sourceId = SourceId . SHA256.hashlazy . toLazyByteString

idBytes :: SourceId -> Builder
idBytes (SourceId b) = varint (toInteger (BS.length b)) <> byteString b

originId :: Origin -> SourceId
originId origin = sourceId $ case origin of
  Declared (Hash h) path i ->
    word8 0
      <> idBytes (SourceId h)
      <> varint (toInteger (length path))
      <> foldMap (sint . toInteger) path
      <> sint (toInteger i)
  Tagged l i -> word8 1 <> text l <> sint (toInteger i)
