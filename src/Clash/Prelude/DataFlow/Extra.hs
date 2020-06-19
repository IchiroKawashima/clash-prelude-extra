{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}

module Clash.Prelude.DataFlow.Extra where

import           Clash.Prelude                  ( HiddenClockResetEnable
                                                , withClockResetEnable
                                                )
import           Clash.Explicit.Prelude
import           Clash.Signal.Internal          ( Signal((:-)) )
import           Control.Monad                  ( guard )
import           Data.Functor                   ( ($>) )
import           Data.Proxy
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH      hiding ( type (<=) )
import           Data.Constraint         hiding ( (&&&) )
import           Data.Constraint.Nat
import qualified Data.List                     as L
import qualified Data.List.Extra               as L
import           Data.Maybe
import           Data.Tuple.Extra
import           Data.Either.Extra
import           GHC.Stack
import           Debug.Trace

decompressLogic :: forall i o
                 . (i -> (o, Maybe i))
                -> Maybe i
                -> (i, Bool, Bool)
                -> (Maybe i, ((Bool, o), Bool, Bool))
decompressLogic f state (iData, iValid, oReady) = (state', ((oLast, oData), oValid, iReady))
  where
    busy         = isJust state

    get          = not busy && iValid && oReady
    put          = (get || busy) && oReady

    oValid       = busy || iValid
    iReady       = not busy && oReady

    preFunc      = fromMaybe iData state
    (oData, acc) = f preFunc
    oLast        = isNothing acc

    state' | put       = acc
           | otherwise = state

decompressInit :: forall i . Maybe i
decompressInit = Nothing

decompressDF :: forall dom i o
              . KnownDomain dom
             => NFDataX i
             => Clock dom
             -> Reset dom
             -> Enable dom
             -> (i -> (o, Maybe i))
             -> DataFlow dom Bool Bool i (Bool, o)
decompressDF clk rst ena f = DF $ curry3 $ mealyB clk rst ena (decompressLogic f) decompressInit
{-# NOINLINE decompressDF #-}

compressLogic :: forall i o
               . (Maybe o -> i -> o)
              -> Maybe o
              -> ((Bool, i), Bool, Bool)
              -> (Maybe o, (o, Bool, Bool))
compressLogic f state (~(iLast, iData), iValid, oReady) = (state', (oData, oValid, iReady))
  where
    busy   = not (iValid && iLast)

    get    = (put || busy) && iValid
    put    = not busy && iValid && oReady

    oValid = not busy && iValid
    iReady = busy || oReady

    postFunc | iValid    = f state iData
             | otherwise = undefined
    (oData, acc) = (postFunc, guard (not put) $> postFunc)

    state' | get       = acc
           | otherwise = state

compressInit :: forall o . Maybe o
compressInit = Nothing

compressDF :: forall dom i o
            . KnownDomain dom
           => NFDataX o
           => Clock dom
           -> Reset dom
           -> Enable dom
           -> (Maybe o -> i -> o)
           -> DataFlow dom Bool Bool (Bool, i) o
compressDF clk rst ena f = DF $ curry3 $ mealyB clk rst ena (compressLogic f) compressInit
{-# NOINLINE compressDF #-}

data UnfoldDF (i :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (UnfoldDF i) _ = i

unfoldDF :: forall dom k i o
          . KnownDomain dom
         => KnownNat k
         => NFDataX o
         => DataFlow dom Bool Bool i (i, i)
         -> DataFlow dom Bool Bool i o
         -> DataFlow dom Bool (Vec (2 ^ k) Bool) i (Vec (2 ^ k) o)
unfoldDF fn = unfoldDF' (Proxy @(UnfoldDF i)) (\SNat -> fn `seqDF` stepLock)
{-# NOINLINE unfoldDF #-}

unfoldDF' :: forall dom p k a
           . KnownDomain dom
          => KnownNat k
          => NFDataX a
          => Proxy p
          -> (  forall l
              . KnownNat l
             => l <= k - 1
             => SNat l
             -> DataFlow
                    dom
                    Bool
                    (Bool, Bool)
                    (p @@ l)
                    (p @@ (l + 1), p @@ (l + 1))
             )
          -> DataFlow dom Bool Bool (p @@ k) a
          -> DataFlow dom Bool (Vec (2 ^ k) Bool) (p @@ 0) (Vec (2 ^ k) a)
unfoldDF' Proxy fn fk = DF $ go SNat
  where
    go :: forall n
        . KnownNat n
       => n <= k
       => SNat n
       -> Signal dom (p @@ (k - n))
       -> Signal dom Bool
       -> Signal dom (Vec (2 ^ n) Bool)
       -> ( Signal dom (Vec (2 ^ n) a)
          , Signal dom (Vec (2 ^ n) Bool)
          , Signal dom Bool
          )
    go SNat d v r@((_ `Cons` Nil) :- _) = (repeat <$> d', repeat <$> v', r')
        where (d', v', r') = df fk d v (head <$> r)
    go SNat d v rs@((_ `Cons` _ `Cons` _) :- _) = case leTrans @(n - 1) @n @k of
        Sub Dict -> (ds, vs, r)
          where
            (unbundle -> (dl, dr), unbundle -> (vl, vr), r ) = df (fn SNat) d v (bundle (rl, rr))

            (dsl                 , vsl                 , rl) = go (SNat @(n - 1)) dl vl rsl
            (dsr                 , vsr                 , rr) = go (SNat @(n - 1)) dr vr rsr

            ds                       = (++) <$> dsl <*> dsr
            vs                       = (++) <$> vsl <*> vsr
            (unbundle -> (rsl, rsr)) = splitAtI <$> rs
    go SNat _ _ _ = undefined
{-# NOINLINE unfoldDF' #-}

data FoldDF (o :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (FoldDF o) _ = o

foldDF :: forall dom k i o
        . KnownDomain dom
       => KnownNat k
       => NFDataX i
       => DataFlow dom Bool Bool i o
       -> DataFlow dom Bool Bool (o, o) o
       -> DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) i) o
foldDF f0 fn = foldDF' (Proxy @(FoldDF o)) f0 (\SNat -> lockStep `seqDF` fn)
{-# NOINLINE foldDF #-}

foldDF' :: forall dom p k a
         . KnownDomain dom
        => KnownNat k
        => NFDataX a
        => Proxy p
        -> DataFlow dom Bool Bool a (p @@ 0)
        -> (  forall l
            . KnownNat l
           => l <= k - 1
           => SNat l
           -> DataFlow dom (Bool, Bool) Bool (p @@ l, p @@ l) (p @@ (l + 1))
           )
        -> DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) a) (p @@ k)
foldDF' Proxy f0 fn = DF $ go SNat
  where
    go :: forall n
        . KnownNat n
       => n <= k
       => SNat n
       -> Signal dom (Vec (2 ^ n) a)
       -> Signal dom (Vec (2 ^ n) Bool)
       -> Signal dom Bool
       -> (Signal dom (p @@ n), Signal dom Bool, Signal dom (Vec (2 ^ n) Bool))
    go SNat d@((_ `Cons` Nil) :- _) v@((_ `Cons` Nil) :- _) r = (d', v', repeat <$> r')
        where (d', v', r') = df f0 (head <$> d) (head <$> v) r
    go SNat ds@((_ `Cons` _ `Cons` _) :- _) vs@((_ `Cons` _ `Cons` _) :- _) r =
        case leTrans @(n - 1) @n @k of
            Sub Dict -> (d, v, rs)
              where
                (unbundle -> (dsl, dsr))       = splitAtI <$> ds
                (unbundle -> (vsl, vsr))       = splitAtI <$> vs
                rs                             = (++) <$> rsl <*> rsr

                (dl, vl, rsl                 ) = go (SNat @(n - 1)) dsl vsl rl
                (dr, vr, rsr                 ) = go (SNat @(n - 1)) dsr vsr rr

                (d , v , unbundle -> (rl, rr)) = df (fn SNat) (bundle (dl, dr)) (bundle (vl, vr)) r
    go SNat _ _ _ = undefined
{-# NOINLINE foldDF' #-}

class SelectStep xEn x x' where
    selectStep :: DataFlow dom xEn Bool x x'
    stepSelect :: DataFlow dom Bool xEn x' x

instance SelectStep Bool x x where
    selectStep = idDF
    stepSelect = idDF

prior :: forall dom . Signal dom Bool
prior = pure False

instance (SelectStep xEn x x', SelectStep yEn y y') => SelectStep (xEn, yEn) (x, y) (Either x' y')
  where
    selectStep = (selectStep `parDF` selectStep) `seqDF` step
      where
        step = DF $ \(unbundle -> (idatA, idatB)) (unbundle -> (ivldA, ivldB)) ordyC ->
            let sel   = not <$> ivldA .&&. (ivldB .||. prior)
                ovldC = mux sel ivldB ivldA
                irdyA = ordyC .&&. not <$> sel
                irdyB = ordyC .&&. sel
                odatC = mux sel (Right <$> idatB) (Left <$> idatA)
            in  (odatC, ovldC, bundle (irdyA, irdyB))

    stepSelect = step `seqDF` (stepSelect `parDF` stepSelect)
      where
        step = DF $ \idatA ivldA (unbundle -> (ordyB, ordyC)) ->
            let sel   = mux ivldA (isRight <$> idatA) prior
                ovldB = ivldA .&&. not <$> sel
                ovldC = ivldA .&&. sel
                irdyA = mux sel ordyC ordyB
                odatB = fromLeft undefined <$> idatA
                odatC = fromRight undefined <$> idatA
            in  (bundle (odatB, odatC), bundle (ovldB, ovldC), irdyA)

selDF :: forall dom a b c d
       . DataFlow dom Bool Bool a b
      -> DataFlow dom Bool Bool c d
      -> DataFlow dom Bool Bool (Either a c) (Either b d)
f `selDF` g = stepSelect `seqDF` (f `parDF` g) `seqDF` selectStep

leftDF :: forall dom a b c
        . DataFlow dom Bool Bool a b
       -> DataFlow dom Bool Bool (Either a c) (Either b c)
leftDF f = f `selDF` idDF

rightDF :: forall dom a b c
         . DataFlow dom Bool Bool a b
        -> DataFlow dom Bool Bool (Either c a) (Either c b)
rightDF g = idDF `selDF` g

justDF :: forall dom a b . DataFlow dom Bool Bool a b -> DataFlow dom Bool Bool (Maybe a) (Maybe b)
justDF f = pureDF (maybeToEither ()) `seqDF` rightDF f `seqDF` pureDF eitherToMaybe

flipDF :: forall dom a b . DataFlow dom Bool Bool (Either a b) (Either b a)
flipDF = DF $ \idat ivld ordy -> (flipEither <$> idat, ivld, ordy)
  where
    flipEither (Left  x) = Right x
    flipEither (Right x) = Left x

parDF' :: forall dom a b c d
        . DataFlow dom Bool Bool a b
       -> DataFlow dom Bool Bool c d
       -> DataFlow dom Bool Bool (a, c) (b, d)
f `parDF'` g = stepLock `seqDF` (f `parDF` g) `seqDF` lockStep

firstDF' :: forall dom a b c . DataFlow dom Bool Bool a b -> DataFlow dom Bool Bool (a, c) (b, c)
firstDF' f = f `parDF'` idDF

secondDF' :: forall dom a b c . DataFlow dom Bool Bool a b -> DataFlow dom Bool Bool (c, a) (c, b)
secondDF' g = idDF `parDF'` g

swapDF' :: forall dom a b . DataFlow dom Bool Bool (a, b) (b, a)
swapDF' = DF $ \idat ivld ordy -> (swapTuple <$> idat, ivld, ordy)
    where swapTuple ~(a, b) = (b, a)

sourceDF :: forall dom en a b . DataFlow dom en (Bool, en) a (b, a)
sourceDF =
    (DF $ \d v (unbundle -> (_, r)) -> (bundle (pure undefined, d), bundle (pure undefined, v), r))
        `seqDF` firstDF (DF $ \_ _ _ -> (pure undefined, pure False, pure undefined))

sinkDF :: forall dom en a b . DataFlow dom (Bool, en) en (b, a) a
sinkDF =
    firstDF (DF $ \_ _ _ -> (pure undefined, pure undefined, pure True))
        `seqDF` (DF $ \(unbundle -> (_, d)) (unbundle -> (_, v)) r ->
                    (d, v, bundle (pure undefined, r))
                )

traceDF :: forall dom en a
         . KnownDomain dom
        => ShowX en
        => ShowX a
        => NFDataX en
        => NFDataX a
        => Clock dom
        -> Reset dom
        -> Enable dom
        -> String
        -> DataFlow dom en en a a
traceDF clk rst ena name = DF $ \idata ivld ordy -> unbundle $ do
    d  <- idata
    v  <- ivld
    r  <- ordy
    d' <- register clk rst ena undefined idata
    v' <- register clk rst ena undefined ivld
    r' <- register clk rst ena undefined ordy

    pure $ trace (name <> ": " <> showX (d', v', r')) (d, v, r)

ramDF :: forall dom n a
       . HasCallStack
      => KnownDomain dom
      => KnownNat n
      => NFDataX a
      => Clock dom
      -> Reset dom
      -> Enable dom
      -> Vec (2 ^ n) a
      -> DataFlow dom (Bool, Bool) Bool ((Unsigned n, a), Unsigned n) a
ramDF clk rst ena mem =
    DF $ \(unbundle -> (iwadrdat, iradr)) (unbundle -> (iwvld, irvld)) orrdy ->
        let ordat =
                    readNew clk rst ena (blockRamPow2 clk ena mem) iradr
                        $   ($>)
                        <$> (guard <$> iwvld)
                        <*> iwadrdat
            orvld = register clk rst ena False irvld
            iwrdy = pure True
            irrdy = orrdy
        in  (ordat, orvld, bundle (iwrdy, irrdy))

$(singletons [d| data QueueMode = None | Mono | Multi |])

queueDF :: forall dom mode a
         . HasCallStack
        => KnownDomain dom
        => NFDataX a
        => Clock dom
        -> Reset dom
        -> Enable dom
        -> SQueueMode mode
        -> DataFlow dom Bool Bool a a
queueDF clk rst ena mode = case mode of
    SNone -> idDF

    SMono -> DF $ \idat ivld ordy ->
        let lock = not <$> busy .&&. ivld
            free = busy .&&. ordy
            busy = register clk rst ena False $ mux busy (not <$> free) lock
            temp = regEn clk rst ena undefined lock idat
        in  (temp, busy, not <$> busy)

    SMulti -> DF $ \idat ivld ordy ->
        let lock0 = ivld .||. busy1
            lock1 = ivld .&&. not <$> ordy .&&. busy0
            free0 = ordy .&&. not <$> ivld .&&. not <$> busy1
            free1 = ordy .||. not <$> busy0
            busy0 = register clk rst ena False $ mux busy0 (not <$> free0) lock0
            busy1 = register clk rst ena False $ mux busy1 (not <$> free1) lock1
            temp0 = regEn clk rst ena undefined (lock0 .&&. free1) $ mux busy1 temp1 idat
            temp1 = regEn clk rst ena undefined (lock1 .&&. not <$> busy1) idat
        in  (temp0, busy0, not <$> busy1)

simulateDF :: forall dom a b
            . KnownDomain dom
           => NFDataX a
           => NFDataX b
           => (HiddenClockResetEnable dom => DataFlow dom Bool Bool a b)
           -> [a]
           -> [(Int, b)]
simulateDF f x = L.zip (L.last $ sampleN len vsig) (L.last $ sampleN len osig)
  where
    clk = clockGen
    rst = resetGen
    ena = enableGen
    cnt = register clk rst ena 0 $ succ <$> cnt

    (odat, ovld, irdy) =
        df (withClockResetEnable clk rst ena f) (L.head <$> isig) (pure True) (pure True)

    isig = regEn clk rst ena x irdy $ L.tail <$> isig
    osig = regEn clk rst ena [] ovld $ L.snoc <$> osig <*> odat
    vsig = register clk rst ena [] $ mux ovld (L.snoc <$> vsig <*> cnt) vsig

    hits = regEn clk rst ena 0 ovld $ succ <$> hits
    len  = succ $ L.length $ L.takeWhile (< L.length x) $ sample hits
