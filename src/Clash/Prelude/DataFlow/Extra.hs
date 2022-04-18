{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Clash.Prelude.DataFlow.Extra where

import Clash.Explicit.Prelude
import Clash.Prelude (HiddenClockResetEnable, withClockResetEnable)
import Clash.Prelude.DataFlow
import Clash.Signal.Internal (Signal ((:-)))
import Control.Monad (guard)
import Data.Constraint hiding ((&&&))
import Data.Constraint.Nat
import Data.Either.Extra
import Data.Functor (($>))
import Data.Kind
import qualified Data.List as L
import Data.Maybe
import Data.Proxy
import Data.Singletons
import Data.Singletons.TH
import Data.Tuple.Extra
import Debug.Trace
import GHC.Stack

decompressLogic ::
  forall i o.
  (i -> (o, Maybe i)) ->
  Maybe i ->
  (i, Bool, Bool) ->
  (Maybe i, ((Bool, o), Bool, Bool))
decompressLogic f state (iData, iValid, oReady) = (state', ((oLast, oData), oValid, iReady))
  where
    busy = isJust state

    get = not busy && iValid && oReady
    put = (get || busy) && oReady

    oValid = busy || iValid
    iReady = not busy && oReady

    preFunc = fromMaybe iData state
    (oData, acc) = f preFunc
    oLast = isNothing acc

    state'
      | put = acc
      | otherwise = state

decompressInit :: forall i. Maybe i
decompressInit = Nothing

decompressDF ::
  forall dom i o.
  KnownDomain dom =>
  NFDataX i =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  (i -> (o, Maybe i)) ->
  DataFlow dom Bool Bool i (Bool, o)
decompressDF clk rst ena f = DF $ curry3 $ mealyB clk rst ena (decompressLogic f) decompressInit

compressLogic ::
  forall i o.
  (Maybe o -> i -> o) ->
  Maybe o ->
  ((Bool, i), Bool, Bool) ->
  (Maybe o, (o, Bool, Bool))
compressLogic f state (~(iLast, iData), iValid, oReady) = (state', (oData, oValid, iReady))
  where
    busy = not (iValid && iLast)

    get = (put || busy) && iValid
    put = not busy && iValid && oReady

    oValid = not busy && iValid
    iReady = busy || oReady

    postFunc
      | iValid = f state iData
      | otherwise = undefined
    (oData, acc) = (postFunc, guard (not put) $> postFunc)

    state'
      | get = acc
      | otherwise = state

compressInit :: forall o. Maybe o
compressInit = Nothing

compressDF ::
  forall dom i o.
  KnownDomain dom =>
  NFDataX o =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  (Maybe o -> i -> o) ->
  DataFlow dom Bool Bool (Bool, i) o
compressDF clk rst ena f = DF $ curry3 $ mealyB clk rst ena (compressLogic f) compressInit

data UnfoldDF (i :: Type) (f :: TyFun Nat Type) :: Type

type instance Apply (UnfoldDF i) _ = i

unfoldDF ::
  forall dom k i o.
  KnownDomain dom =>
  KnownNat k =>
  NFDataX o =>
  DataFlow dom Bool Bool i (i, i) ->
  DataFlow dom Bool Bool i o ->
  DataFlow dom Bool (Vec (2 ^ k) Bool) i (Vec (2 ^ k) o)
unfoldDF fn = unfoldDF' (Proxy @(UnfoldDF i)) (\SNat -> fn `seqDF` stepLock)

unfoldDF' ::
  forall dom p k a.
  KnownDomain dom =>
  KnownNat k =>
  NFDataX a =>
  Proxy p ->
  ( forall l.
    KnownNat l =>
    l <= k - 1 =>
    SNat l ->
    DataFlow
      dom
      Bool
      (Bool, Bool)
      (p @@ l)
      (p @@ (l + 1), p @@ (l + 1))
  ) ->
  DataFlow dom Bool Bool (p @@ k) a ->
  DataFlow dom Bool (Vec (2 ^ k) Bool) (p @@ 0) (Vec (2 ^ k) a)
unfoldDF' Proxy fn fk = DF $ go SNat
  where
    go ::
      forall n.
      KnownNat n =>
      n <= k =>
      SNat n ->
      Signal dom (p @@ (k - n)) ->
      Signal dom Bool ->
      Signal dom (Vec (2 ^ n) Bool) ->
      ( Signal dom (Vec (2 ^ n) a),
        Signal dom (Vec (2 ^ n) Bool),
        Signal dom Bool
      )
    go SNat d v r@((_ `Cons` Nil) :- _) = (repeat <$> d', repeat <$> v', r')
      where
        (d', v', r') = df fk d v (head <$> r)
    go SNat d v rs@((_ `Cons` _ `Cons` _) :- _) = case leTrans @(n - 1) @n @k of
      Sub Dict -> (ds, vs, r)
        where
          (unbundle -> (dl, dr), unbundle -> (vl, vr), r) = df (fn SNat) d v (bundle (rl, rr))

          (dsl, vsl, rl) = go (SNat @(n - 1)) dl vl rsl
          (dsr, vsr, rr) = go (SNat @(n - 1)) dr vr rsr

          ds = (++) <$> dsl <*> dsr
          vs = (++) <$> vsl <*> vsr
          (unbundle -> (rsl, rsr)) = splitAtI <$> rs
    go SNat _ _ _ = undefined

data FoldDF (o :: Type) (f :: TyFun Nat Type) :: Type

type instance Apply (FoldDF o) _ = o

foldDF ::
  forall dom k i o.
  KnownDomain dom =>
  KnownNat k =>
  NFDataX i =>
  DataFlow dom Bool Bool i o ->
  DataFlow dom Bool Bool (o, o) o ->
  DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) i) o
foldDF f0 fn = foldDF' (Proxy @(FoldDF o)) f0 (\SNat -> lockStep `seqDF` fn)

foldDF' ::
  forall dom p k a.
  KnownDomain dom =>
  KnownNat k =>
  NFDataX a =>
  Proxy p ->
  DataFlow dom Bool Bool a (p @@ 0) ->
  ( forall l.
    KnownNat l =>
    l <= k - 1 =>
    SNat l ->
    DataFlow dom (Bool, Bool) Bool (p @@ l, p @@ l) (p @@ (l + 1))
  ) ->
  DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) a) (p @@ k)
foldDF' Proxy f0 fn = DF $ go SNat
  where
    go ::
      forall n.
      KnownNat n =>
      n <= k =>
      SNat n ->
      Signal dom (Vec (2 ^ n) a) ->
      Signal dom (Vec (2 ^ n) Bool) ->
      Signal dom Bool ->
      (Signal dom (p @@ n), Signal dom Bool, Signal dom (Vec (2 ^ n) Bool))
    go SNat d@((_ `Cons` Nil) :- _) v@((_ `Cons` Nil) :- _) r = (d', v', repeat <$> r')
      where
        (d', v', r') = df f0 (head <$> d) (head <$> v) r
    go SNat ds@((_ `Cons` _ `Cons` _) :- _) vs@((_ `Cons` _ `Cons` _) :- _) r =
      case leTrans @(n - 1) @n @k of
        Sub Dict -> (d, v, rs)
          where
            (unbundle -> (dsl, dsr)) = splitAtI <$> ds
            (unbundle -> (vsl, vsr)) = splitAtI <$> vs
            rs = (++) <$> rsl <*> rsr

            (dl, vl, rsl) = go (SNat @(n - 1)) dsl vsl rl
            (dr, vr, rsr) = go (SNat @(n - 1)) dsr vsr rr

            (d, v, unbundle -> (rl, rr)) = df (fn SNat) (bundle (dl, dr)) (bundle (vl, vr)) r
    go SNat _ _ _ = undefined

sourceDF :: forall dom en a b. b -> DataFlow dom en (Bool, en) a (b, a)
sourceDF dat =
  DF (\d v (unbundle -> (_, r)) -> (bundle (pure undefined, d), bundle (pure undefined, v), r))
    `seqDF` firstDF (DF $ \_ _ _ -> (pure dat, pure True, pure undefined))

sinkDF :: forall dom en a b. DataFlow dom (Bool, en) en (b, a) a
sinkDF =
  firstDF (DF $ \_ _ _ -> (pure undefined, pure undefined, pure True))
    `seqDF` DF (\(unbundle -> (_, d)) (unbundle -> (_, v)) r -> (d, v, bundle (pure undefined, r)))

traceDF ::
  forall dom en a.
  KnownDomain dom =>
  ShowX en =>
  ShowX a =>
  NFDataX en =>
  NFDataX a =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  String ->
  DataFlow dom en en a a
traceDF clk rst ena name = DF $ \idata ivld ordy -> unbundle $ do
  d <- idata
  v <- ivld
  r <- ordy
  d' <- register clk rst ena undefined idata
  v' <- register clk rst ena undefined ivld
  r' <- register clk rst ena undefined ordy

  pure $ trace (name <> ": " <> showX (d', v', r')) (d, v, r)

ramDF ::
  forall dom n a.
  HasCallStack =>
  KnownDomain dom =>
  KnownNat n =>
  NFDataX a =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  Vec (2 ^ n) a ->
  Signal dom (Maybe (Unsigned n, a)) ->
  DataFlow dom Bool Bool (Unsigned n) a
ramDF clk rst ena mem iwdat = DF $ \iadr ivld ordy ->
  let lock0 = ivld .||. busy1
      lock1 = ivld .&&. not <$> ordy .&&. busy0
      free0 = ordy .&&. not <$> ivld .&&. not <$> busy1
      free1 = ordy .||. not <$> busy0
      busy0 = register clk rst ena False $ mux busy0 (not <$> free0) lock0
      busy1 = register clk rst ena False $ mux busy1 (not <$> free1) lock1
      temp0 = mux (lock0 .&&. free1) (mux busy1 temp1 iadr) $ register clk rst ena undefined temp0
      temp1 = regEn clk rst ena undefined (lock1 .&&. not <$> busy1) iadr
      ordat = readNew clk rst ena (blockRamPow2 clk ena mem) temp0 iwdat
   in (ordat, busy0, not <$> busy1)

regDF ::
  forall dom a.
  HasCallStack =>
  KnownDomain dom =>
  NFDataX a =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  a ->
  DataFlow dom Bool Bool a a
regDF clk rst ena ini = DF $ \idat ivld ordy ->
  let lock0 = ivld .||. busy1
      lock1 = ivld .&&. not <$> ordy .&&. busy0
      free0 = ordy .&&. not <$> ivld .&&. not <$> busy1
      free1 = ordy .||. not <$> busy0
      busy0 = register clk rst ena True $ mux busy0 (not <$> free0) lock0
      busy1 = register clk rst ena False $ mux busy1 (not <$> free1) lock1
      temp0 = regEn clk rst ena ini (lock0 .&&. (ordy .||. not <$> busy0)) $ mux busy1 temp1 idat
      temp1 = regEn clk rst ena undefined (lock1 .&&. not <$> busy1) idat
   in (temp0, busy0, not <$> busy1)

$(singletons [d|data QueueMode = None | Mono | Multi|])

queueDF ::
  forall dom mode a.
  HasCallStack =>
  KnownDomain dom =>
  NFDataX a =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  SQueueMode mode ->
  DataFlow dom Bool Bool a a
queueDF clk rst ena mode = case mode of
  SNone -> idDF
  SMono -> DF $ \idat ivld ordy ->
    let lock = not <$> busy .&&. ivld
        free = busy .&&. ordy
        busy = register clk rst ena False $ mux busy (not <$> free) lock
        temp = regEn clk rst ena undefined lock idat
     in (temp, busy, not <$> busy)
  SMulti -> DF $ \idat ivld ordy ->
    let lock0 = ivld .||. busy1
        lock1 = ivld .&&. not <$> ordy .&&. busy0
        free0 = ordy .&&. not <$> ivld .&&. not <$> busy1
        free1 = ordy .||. not <$> busy0
        busy0 = register clk rst ena False $ mux busy0 (not <$> free0) lock0
        busy1 = register clk rst ena False $ mux busy1 (not <$> free1) lock1
        temp0 =
          regEn clk rst ena undefined (lock0 .&&. (ordy .||. not <$> busy0)) $
            mux busy1 temp1 idat
        temp1 = regEn clk rst ena undefined (lock1 .&&. not <$> busy1) idat
     in (temp0, busy0, not <$> busy1)

class SelectStep xEn x where
  type Select xEn x :: Type
  selectStep :: DataFlow dom xEn Bool (Select xEn x) x
  stepSelect :: DataFlow dom Bool xEn x (Select xEn x)

instance SelectStep Bool x where
  type Select Bool x = x
  selectStep = idDF
  stepSelect = idDF

prior :: forall dom. Signal dom Bool
prior = pure False

instance (SelectStep xEn x, SelectStep yEn y) => SelectStep (xEn, yEn) (Either x y) where
  type Select (xEn, yEn) (Either x y) = (Select xEn x, Select yEn y)

  selectStep = (selectStep `parDF` selectStep) `seqDF` step
    where
      step = DF $ \(unbundle -> (idatA, idatB)) (unbundle -> (ivldA, ivldB)) ordyC ->
        let sel = not <$> ivldA .&&. (ivldB .||. prior)
            ovldC = mux sel ivldB ivldA
            irdyA = ordyC .&&. not <$> sel
            irdyB = ordyC .&&. sel
            odatC = mux sel (Right <$> idatB) (Left <$> idatA)
         in (odatC, ovldC, bundle (irdyA, irdyB))

  stepSelect = step `seqDF` (stepSelect `parDF` stepSelect)
    where
      step = DF $ \idatA ivldA (unbundle -> (ordyB, ordyC)) ->
        let sel = mux ivldA (isRight <$> idatA) prior
            ovldB = ivldA .&&. not <$> sel
            ovldC = ivldA .&&. sel
            irdyA = mux sel ordyC ordyB
            odatB = fromLeft undefined <$> idatA
            odatC = fromRight undefined <$> idatA
         in (bundle (odatB, odatC), bundle (ovldB, ovldC), irdyA)

testDF ::
  forall dom m n a b.
  HasCallStack =>
  KnownDomain dom =>
  KnownNat m =>
  KnownNat n =>
  NFDataX a =>
  NFDataX b =>
  Clock dom ->
  Reset dom ->
  Enable dom ->
  Int ->
  (HiddenClockResetEnable dom => DataFlow dom Bool Bool a b) ->
  Vec m a ->
  Vec m Int ->
  ((Signal dom Bool, Signal dom Bool), (Signal dom (Vec n b), Signal dom (Vec n Int)))
testDF clk rst ena n f (pure -> x) (pure -> i) = ((done, term), unbundle $ unzip <$> y)
  where
    cnt = register clk rst ena 0 $ succ <$> cnt

    (odat, ovld, irdy) = df (withClockResetEnable clk rst ena f) idat ivld ordy

    idat = mux (ivld .&&. irdy) ((!!) <$> x <*> iptr) (pure undefined)
    ivld = ((/= snatToInteger (SNat @m)) <$> iptr) .&&. sleep
    ordy = ((/= snatToInteger (SNat @n)) <$> optr)

    sleep = (cnt - 1) - xcnt .>=. ((!!) <$> i <*> iptr)
    xcnt = regEn clk rst ena (-1) (ivld .&&. irdy) cnt
    ycnt = regEn clk rst ena (-1) (ovld .&&. ordy) cnt

    iptr = regEn clk rst ena 0 (ivld .&&. irdy) $ succ <$> iptr
    optr = regEn clk rst ena 0 (ovld .&&. ordy) $ succ <$> optr

    y = register clk rst ena (repeat (undefined, undefined)) y'
    y' = mux (ovld .&&. ordy) (replace <$> optr <*> ((,) <$> odat <*> (cnt - 1) - ycnt) <*> y) y

    done = not <$> ordy
    term = (>= n) <$> cnt

simulateDF ::
  forall dom m n a b.
  HasCallStack =>
  KnownDomain dom =>
  KnownNat m =>
  KnownNat n =>
  NFDataX a =>
  NFDataX b =>
  Int ->
  (HiddenClockResetEnable dom => DataFlow dom Bool Bool a b) ->
  Vec m a ->
  Vec m Int ->
  (Vec n b, Vec n Int)
simulateDF n f x i = (sample y L.!! cnt, sample i' L.!! cnt)
  where
    clk = clockGen
    rst = resetGen
    ena = enableGen

    ((fin, (y, i'))) = testDF clk rst ena n f x i
    cnt = uncurry min $ both (L.length . L.takeWhile not . sample) fin
