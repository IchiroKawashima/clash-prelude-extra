module Clash.Prelude.Extra
  ( module Exports,
  )
where

import Clash.Prelude.DataFlow.Extra as Exports
  ( SQueueMode (..),
    SelectStep (..),
    compressDF,
    decompressDF,
    firstDF',
    flipDF,
    foldDF,
    foldDF',
    justDF,
    justDF',
    leftDF,
    leftDF',
    parDF',
    queueDF,
    ramDF,
    rightDF,
    rightDF',
    secondDF',
    selDF,
    selDF',
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
