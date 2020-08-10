module Clash.Sized.Vector.Extra where

import           Clash.Prelude
import           Data.Proxy
import           Data.Singletons
import           Data.Constraint
import           Data.Constraint.Nat
import           Data.Constraint.Nat.Extra

dfold' :: forall p k a
        . KnownNat k
       => Proxy p
       -> (forall l . KnownNat l => l <= k - 1 => SNat l -> a -> p @@ l -> p @@ (l + 1))
       -> (p @@ 0)
       -> Vec k a
       -> (p @@ k)
dfold' Proxy f z = go
  where
    go :: forall n . KnownNat n => n <= k => Vec n a -> p @@ n
    go Nil           = z
    go (y `Cons` ys) = case subMonotone1 @n @k @1 of
        Sub Dict -> f SNat y (go ys)
{-# NOINLINE dfold' #-}

dtfold' :: forall p k a
         . (KnownNat k)
        => Proxy p
        -> (a -> p @@ 0)
        -> (  forall l
            . KnownNat l
           => l <= k - 1 => SNat l -> p @@ l -> p @@ l -> p @@ (l + 1)
           )
        -> Vec (2 ^ k) a
        -> (p @@ k)
dtfold' Proxy f0 fn = go
  where
    go :: forall n . KnownNat n => n <= k => Vec (2 ^ n) a -> p @@ n
    go (   x          `Cons` Nil) = f0 x
    go xs@(_ `Cons` _ `Cons` _  ) = case leTrans @(n - 1) @n @k of
        Sub Dict -> fn SNat (go xsl) (go xsr) where (xsl, xsr) = splitAtI xs
    go _ = undefined
{-# NOINLINE dtfold' #-}
