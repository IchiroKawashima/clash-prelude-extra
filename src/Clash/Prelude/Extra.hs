module Clash.Prelude.Extra
  ( module Exports,
  )
where

import Clash.Prelude.DataFlow.Extra as Exports
  ( QueueMode (..),
    SQueueMode (..),
    SelectStep (..),
    compressDF,
    decompressDF,
    foldDF,
    foldDF',
    queueDF,
    ramDF,
    regDF,
    simulateDF,
    sinkDF,
    sourceDF,
    testDF,
    traceDF,
    unfoldDF,
    unfoldDF',
  )
import Clash.Promoted.Nat.Extra as Exports
  ( PowerOf,
  )
import Clash.Sized.Fixed.Extra as Exports
  ( absolute,
    boundF,
    negative,
    positive,
    signed,
    unsigned,
  )
import Clash.Sized.Index.Extra as Exports
  ( i2bv,
  )
import Clash.Sized.Vector.Extra as Exports
  ( dfold',
    dtfold',
  )
