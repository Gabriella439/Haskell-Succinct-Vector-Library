{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--real" @-}

module Poppy2 where

import Data.Word (Word64)
import Poppy

import qualified Data.Vector
import qualified Data.Vector.Primitive
import qualified Primitives

{-@
unsafeRank
    :: sbv : SuccinctBitVector
    -> { bit : Int | 0 <= bit && bit <= plen (vector sbv) * 64 }
    -> Word64
@-}
unsafeRank :: SuccinctBitVector -> Int -> Word64
unsafeRank sbv@(SuccinctBitVector {..}) p0 = c0 + c1 + c2 + c3
  where
    -- TODO: Use `quotRem` when Liquid Haskell Prelude is fixed
    p1   = p0 `div` 4294967296

    p2   = p0 `div` 2048
    q2   = p0 `mod` 2048

    p3   = q2 `div` 512
    q3   = q2 `mod` 512

    p4   = q3 `div` 64

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
                    (((p0 - q2) + p3 * 512) `div` 64)
                    p4
                    vector ) )

-- main :: IO ()
-- main = prepare (Data.Vector.Primitive.enumFromN 0 10000000) `seq` return ()

-- unsafeSelect :: SuccinctBitVector -> Word64 -> Int
unsafeSelect (SuccinctBitVector {..}) y0 = (pMin, pMax)
  where
    l0Index = Primitives.search y0 id l0s 0 (Data.Vector.Primitive.length l0s)
    l0      = Data.Vector.Primitive.unsafeIndex l0s l0Index
    y1      = y0 - l0
    pMin    =
        Data.Vector.Primitive.unsafeIndex
            (Data.Vector.unsafeIndex sample1s l0Index)
            (fromIntegral ((y1 `div` 8192) * 8192    ))
    pMax    =
        Data.Vector.Primitive.unsafeIndex
            (Data.Vector.unsafeIndex sample1s l0Index)
            (fromIntegral ((y1 `div` 8192) * 8192 + 1))
{-
    pMax = Data.Vector.Primitive.unsafeIndex sample1s (fromIntegral ((y1 `div` 8192) * 8192 + 1))
    l1Lo = Data.Vector.Primitive.unsafeIndex l1l2s    (pMin `div` 2048)
    l1Hi = Data.Vector.Primitive.unsafeIndex l1l2s    (pMax `div` 2048)
    l1l2 = search 
-}
