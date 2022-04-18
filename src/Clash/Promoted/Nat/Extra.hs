module Clash.Promoted.Nat.Extra where

import Clash.Prelude

type PowerOf m n = (1 <= n, FLog m n ~ CLog m n)
