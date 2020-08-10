module Clash.Prelude.Extra
    ( module Exports
    )
where

import           Clash.Prelude.DataFlow.Extra  as Exports
                                                ( decompressDF
                                                , compressDF
                                                , unfoldDF
                                                , unfoldDF'
                                                , foldDF
                                                , foldDF'
                                                , sourceDF
                                                , sinkDF
                                                , traceDF
                                                , ramDF
                                                , SQueueMode(..)
                                                , queueDF
                                                , SelectStep(..)
                                                , selDF
                                                , leftDF
                                                , rightDF
                                                , justDF
                                                , flipDF
                                                , selDF'
                                                , leftDF'
                                                , rightDF'
                                                , justDF'
                                                , parDF'
                                                , firstDF'
                                                , secondDF'
                                                , testDF
                                                , simulateDF
                                                )
import           Clash.Sized.Index.Extra       as Exports
                                                ( i2bv )
import           Clash.Sized.Fixed.Extra       as Exports
                                                ( signed
                                                , unsigned
                                                , absolute
                                                , positive
                                                , negative
                                                , boundF
                                                )
import           Clash.Sized.Vector.Extra      as Exports
                                                ( dfold'
                                                , dtfold'
                                                )
import           Clash.Promoted.Nat.Extra      as Exports
                                                ( PowerOf )
