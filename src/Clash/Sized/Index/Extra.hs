module Clash.Sized.Index.Extra where

import           Clash.Prelude

i2bv :: forall n . KnownNat n => Index (2 ^ n) -> BitVector n
i2bv = pack
