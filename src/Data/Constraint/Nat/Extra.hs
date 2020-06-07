{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Constraint.Nat.Extra
    ( subMonotone1
    , subMonotone2
    )
where

import           Data.Constraint
import           GHC.TypeLits
import           Unsafe.Coerce

axiom :: forall a b . Dict (a ~ b)
axiom = unsafeCoerce (Dict @(a ~ a))

subMonotone1 :: forall a b c . (a <= b, c <= a) :- (a - c <= b - c)
subMonotone1 = Sub axiom

subMonotone2 :: forall a b c . (c <= b, b <= a) :- (a - b <= a - c)
subMonotone2 = Sub axiom
