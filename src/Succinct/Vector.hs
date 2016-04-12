{-# LANGUAGE RecordWildCards #-}

module Succinct.Vector (
      module Succinct.Vector
    , module Succinct.Vector.Index
    ) where

import Data.Bits ((.&.))
import Data.Word (Word32, Word64)
import Succinct.Vector.Index

import qualified Data.Vector
import qualified Data.Vector.Primitive
import qualified Succinct.Vector.Primitives as Primitives

{-@
unsafeRank
    :: sbv : SuccinctBitVector
    -> { bit : Int | 0 <= bit && bit < plen (vector sbv) * 64 }
    -> Word64
@-}
unsafeRank :: SuccinctBitVector -> Int -> Word64
unsafeRank sbv@(SuccinctBitVector {..}) p0 =
    case p0 `quotRem` 2048 of
        (p2, q2) -> case q2 `quotRem` 512 of
            (p3, q3) -> c0 + c1 + c2 + c3 + c4
              where
                p1       = p0 `quot` 4294967296

                c0   = Data.Vector.Primitive.unsafeIndex l0s   p1

                l1l2 = Data.Vector.Primitive.unsafeIndex l1l2s p2

                c1   = l1 l1l2

                c2   = case p3 of
                    0 -> 0
                    1 -> l2_0 l1l2
                    2 -> l2_0 l1l2 + l2_1 l1l2
                    _ -> l2_0 l1l2 + l2_1 l1l2 + l2_2 l1l2

                c3   =
                    Data.Vector.Primitive.sum
                        (Data.Vector.Primitive.map popCount
                            (Data.Vector.Primitive.unsafeSlice
                                (((p0 - q2) + p3 * 512) `quot` 64)
                                (q3 `quot` 64)
                                vector ) )

                c4   = case p0 `quotRem` 64 of
                    (p, q) -> popCount (Data.Vector.Primitive.unsafeIndex vector p .&. mask)
                      where
                        mask = (1 << q) - 1
{-# INLINABLE unsafeRank #-}

{-@ assume word64ToInt :: Word64 -> { n : Int | 0 <= n } @-}
word64ToInt :: Word64 -> Int
word64ToInt = fromIntegral
{-# INLINE word64ToInt #-}

{-@ assume word32ToInt :: Word32 -> { n : Int | 0 <= n && n < 4294967296 } @-}
word32ToInt :: Word32 -> Int
word32ToInt = fromIntegral
{-# INLINE word32ToInt #-}

{-@ assume assumeLessThan :: x : Int -> y : Int -> { v : () | x < y } @-}
assumeLessThan :: Int -> Int -> ()
assumeLessThan _ _ = ()
{-# INLINE assumeLessThan #-}

{-
unsafeSelect
    :: sbv : SuccinctBitVector
    -> { y0  : Word64 | 0 <= y0 }
    -> (Word32, Word32)
-}
unsafeSelect :: SuccinctBitVector -> Word64 -> Int
unsafeSelect (SuccinctBitVector {..}) y0 =
      l1l2Index * 2048
    + l2Index   * 512
    + l3Index   * 64
    + l4Index
  where
    l0Index = Primitives.search y0 id l0s 0 (Data.Vector.Primitive.length l0s)
    l0      = Data.Vector.Primitive.unsafeIndex l0s      l0Index
    samples = Data.Vector.unsafeIndex           sample1s l0Index

    {-@
    safeSample
        :: { i : Int | 0 <= i } -> { n : Int | 0 <= n && n <= 4294967296 }
    @-}
    safeSample :: Int -> Int
    safeSample i =
        if i < Data.Vector.Primitive.length samples
        then word32ToInt (Data.Vector.Primitive.unsafeIndex samples i)
        else 4294967296

    y1          = y0 - l0
    sampleIndex = y1 `quot` 8192
    sampleMin   = l0Index * 4294967296 + safeSample (word64ToInt  sampleIndex     )
    sampleMax   = l0Index * 4294967296 + safeSample (word64ToInt (sampleIndex + 1))

    -- TODO: Prove that `l1l2IndexMin` is in bounds without using `min`
    l1l2IndexMin =
        min ( sampleMin      `quot` 2048    )
            (Data.Vector.Primitive.length l1l2s - 1)
    l1l2IndexMax =
        min ((sampleMax - 1) `quot` 2048 + 1)
            (Data.Vector.Primitive.length l1l2s)
    l1l2Index    =
        assumeLessThan sampleMin sampleMax `seq`
        Primitives.search y1 l1 l1l2s l1l2IndexMin l1l2IndexMax
    l1l2         = Data.Vector.Primitive.unsafeIndex l1l2s l1l2Index
    l1_          = l1 l1l2

    y2    = y1 - l1_
    l2_0_ = l2_0 l1l2
    l2_1_ = l2_1 l1l2
    l2_2_ = l2_2 l1l2
    (l2Index, y3) = do
        if  y2 < l2_0_
        then (0, y2)
        else do
            let y3_0 = y2 - l2_0_
            if  y3_0 < l2_1_
            then (1, y3_0)
            else do
                let y3_1 = y3_0 - l2_1_
                if  y3_1 < l2_2_
                then (2, y3_1)
                else do
                    let y3_2 = y3_1 - l2_2_
                    (3, y3_2)

    l3IndexMin = l1l2Index * 32
               + l2Index   * 8

    w64_0 = Data.Vector.Primitive.unsafeIndex vector  l3IndexMin
    w64_1 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 1)
    w64_2 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 2)
    w64_3 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 3)
    w64_4 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 4)
    w64_5 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 5)
    w64_6 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 6)
    w64_7 = Data.Vector.Primitive.unsafeIndex vector (l3IndexMin + 7)

    n_0 = popCount w64_0
    n_1 = popCount w64_1
    n_2 = popCount w64_2
    n_3 = popCount w64_3
    n_4 = popCount w64_4
    n_5 = popCount w64_5
    n_6 = popCount w64_6

    (w64, l3Index, y4) = do
        if  y3 < n_0
        then (w64_0, 0, y3)
        else do
            let y4_0 = y3 - n_0
            if  y4_0 < n_1
            then (w64_1, 1, y4_0)
            else do
                let y4_1 = y4_0 - n_1
                if  y4_1 < n_2
                then (w64_2, 2, y4_1)
                else do
                    let y4_2 = y4_1 - n_2
                    if  y4_2 < n_3
                    then (w64_3, 3, y4_2)
                    else do
                        let y4_3 = y4_2 - n_3
                        if  y4_3 < n_4
                        then (w64_4, 4, y4_3)
                        else do
                            let y4_4 = y4_3 - n_4
                            if y4_4 < n_5
                            then (w64_5, 5, y4_4)
                            else do
                                let y4_5 = y4_4 - n_5
                                let y4_6 = y4_5 - n_6
                                if  y4_5 < n_6
                                then (w64_6, 6, y4_5)
                                else (w64_7, 7, y4_6)

    l4Index = selectWord64 w64 y4
