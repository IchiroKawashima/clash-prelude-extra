module Clash.Sized.Fixed.Extra where

import Clash.Prelude
import Data.Tuple.Extra

signed ::
  forall int frac.
  (KnownNat int, KnownNat frac) =>
  UFixed int frac ->
  SFixed (1 + int) frac
signed = unpack . resize . pack

unsigned ::
  forall int frac.
  (KnownNat int, KnownNat frac) =>
  SFixed (1 + int) frac ->
  (Bit, UFixed int frac)
unsigned = msb &&& unpack . resize . pack . abs

absolute ::
  forall int frac.
  (KnownNat int, KnownNat frac) =>
  SFixed (1 + int) frac ->
  UFixed int frac
absolute = snd . unsigned

positive ::
  forall int frac.
  (KnownNat int, KnownNat frac) =>
  SFixed (1 + int) frac ->
  UFixed int frac
positive = unpack . resize . pack . max 0

negative ::
  forall int frac.
  (KnownNat int, KnownNat frac) =>
  SFixed (1 + int) frac ->
  UFixed int frac
negative = positive . negate

boundF ::
  forall rep int1 frac1 int2 frac2.
  ResizeFC rep int1 frac1 int2 frac2 =>
  ResizeFC rep int2 frac2 int1 frac1 =>
  Fixed rep int1 frac1 ->
  Fixed rep int2 frac2
boundF =
  resizeF . max (resizeF $ minBound @(Fixed rep int2 frac2))
    . min
      (resizeF $ maxBound @(Fixed rep int2 frac2))
