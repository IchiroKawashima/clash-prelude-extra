{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ApplicativeDo #-}

module Clash.Prelude.DataFlow.Extra where

import           Clash.Prelude           hiding ( last )
import           Clash.Signal.Internal          ( Signal((:-)) )
import           Control.Monad                  ( guard )
import           Data.Functor                   ( ($>) )
import           Data.Proxy
import           Data.Kind
import           Data.Singletons
import           Data.Constraint         hiding ( (&&&) )
import           Data.Constraint.Nat
import           Data.Maybe
import           Data.Tuple.Extra
import           Data.Either.Extra
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
              . HiddenClockResetEnable dom
             => NFDataX i => (i -> (o, Maybe i)) -> DataFlow dom Bool Bool i (Bool, o)
decompressDF f = DF $ curry3 $ decompressLogic f <^> decompressInit
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
            . HiddenClockResetEnable dom
           => NFDataX o => (Maybe o -> i -> o) -> DataFlow dom Bool Bool (Bool, i) o
compressDF f = DF $ curry3 $ compressLogic f <^> compressInit
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

flipDF :: forall dom a b . DataFlow dom Bool Bool (Either a b) (Either b a)
flipDF = DF $ \idat ivld ordy -> (flipEither <$> idat, ivld, ordy)
  where
    flipEither (Left  x) = Right x
    flipEither (Right x) = Left x

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
         . HiddenClockResetEnable dom
        => ShowX en => ShowX a => NFDataX en => NFDataX a => String -> DataFlow dom en en a a
traceDF name = DF $ \idata ivld ordy -> unbundle $ do
    d  <- idata
    v  <- ivld
    r  <- ordy
    d' <- register undefined idata
    v' <- register undefined ivld
    r' <- register undefined ordy

    pure $ trace (name <> ": " <> showX (d', v', r')) (d, v, r)
