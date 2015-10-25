{-| Example usage of this module:

>>> import Data.Vector.Primitive
>>> let v = fromList [maxBound, 0] :: Vector Word64
>>> let idx = prepare v
>>> index idx 63
Just True
>>> index idx 64
Just False
>>> rank idx 27
Just 27
>>> rank idx 128
Just 64

    This module is based on the paper "Broadword Implementation of Rank/Select
    Queries":

    <http://vigna.di.unimi.it/ftp/papers/Broadword.pdf>
-}

module Succinct.Vector (
    -- * Construction
      SuccinctBitVector
    , prepare

    -- * Queries
    , index
    , unsafeIndex
    , rank
    , unsafeRank
    ) where

import Control.DeepSeq (NFData(..))
import Data.Bits ((.|.), (.&.))
import Data.Word (Word64)

import qualified Data.Bits             as Bits
import qualified Data.Vector.Primitive as Primitive

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Vector.Primitive as Primitive
-- >>> import Test.QuickCheck
-- >>> instance (Prim a, Arbitrary a) => Arbitrary (Vector a) where arbitrary = fmap fromList arbitrary

{-| Like `index` except that the bit index is not checked

    This will silently fail and return garbage if you supply an invalid index
-}
unsafeIndex :: SuccinctBitVector -> Int -> Bool
unsafeIndex i n = Bits.testBit w8 r
  where
    (q, r) = quotRem n 64
    w8 = Primitive.unsafeIndex (bits i) q


-- | @(index i n)@ retrieves the bit at the index @n@
index :: SuccinctBitVector -> Int -> Maybe Bool
index i n =
    if 0 <= n && n < size i
    then Just (unsafeIndex i n)
    else Nothing

{-| A bit vector enriched with an index that adds O(1) `rank` and `select`
    queries

    The `SuccinctBitVector` increases the original bit vector's size by 25%
-}
data SuccinctBitVector = SuccinctBitVector
    { size :: {-# UNPACK #-} !Int
    -- ^ Size of original bit vector, in bits
    , idx  :: {-# UNPACK #-} !(Primitive.Vector Word64)
    -- ^ Two-level index of cached rank calculations at Word64 boundaries
    , bits :: {-# UNPACK #-} !(Primitive.Vector Word64)
    -- ^ Original bit vector
    }

instance NFData SuccinctBitVector where
    rnf i = i `seq` ()

data Level = First | Second

data Status = Status
                   !Level
    {-# UNPACK #-} !Word64  -- Current rank
    {-# UNPACK #-} !Int     -- Position in vector

popCount :: Word64 -> Word64
popCount x0 = Bits.unsafeShiftR (x3 * 0x0101010101010101) 56
  where
    x1 = x0 - (Bits.unsafeShiftR (x0 .&. 0xAAAAAAAAAAAAAAAA) 1)
    x2 = (x1 .&. 0x3333333333333333) + ((Bits.unsafeShiftR x1 2) .&. 0x3333333333333333)
    x3 = (x2 + (Bits.unsafeShiftR x2 4)) .&. 0x0F0F0F0F0F0F0F0F

{-| Create an `SuccinctBitVector` from a `Primitive.Vector` of bits packed as
    `Word64`s

    You are responsible for padding your data to the next `Word64` boundary
-}
prepare :: Primitive.Vector Word64 -> SuccinctBitVector
prepare v = SuccinctBitVector
    { size = len * 64
    , idx  = Primitive.unfoldrN iLen iStep iBegin
    , bits = v
    }
  where
    len = Primitive.length v

    iLen = 2 * (((len - 1) `div` 8) + 1) + 1

    iStep (Status level r i0) = Just (case level of
        First  -> (r , Status Second r       i0)
        Second -> (r', Status First (r + r8) i8) )
          where
            i1 = i0 + 1
            i2 = i1 + 1
            i3 = i2 + 1
            i4 = i3 + 1
            i5 = i4 + 1
            i6 = i5 + 1
            i7 = i6 + 1
            i8 = i7 + 1

            count i =
                if i < len
                then popCount (Primitive.unsafeIndex v i)
                else 0

            r1 =      count i0
            r2 = r1 + count i1
            r3 = r2 + count i2
            r4 = r3 + count i3
            r5 = r4 + count i4
            r6 = r5 + count i5
            r7 = r6 + count i6
            r8 = r7 + count i7

            r' = r1
             .|. Bits.unsafeShiftL r2  9
             .|. Bits.unsafeShiftL r3 18
             .|. Bits.unsafeShiftL r4 27
             .|. Bits.unsafeShiftL r5 36
             .|. Bits.unsafeShiftL r6 45
             .|. Bits.unsafeShiftL r7 54

    iBegin = Status First 0 0

{-| Like `rank` except that the bit index is not checked

    This will silently fail and return garbage if you supply an invalid index
-}
unsafeRank :: SuccinctBitVector -> Int -> Word64
unsafeRank (SuccinctBitVector _ idx_ bits_) p =
        f
    +   ((Bits.unsafeShiftR s (fromIntegral ((t + (Bits.unsafeShiftR t 60 .&. 0x8)) * 9))) .&. 0x1FF)
    +   popCount (Primitive.unsafeIndex bits_ w .&. mask)
  where
    (w, b) = quotRem p 64
    (q, r) = quotRem w 8
    f      = Primitive.unsafeIndex idx_ (2 * q    )
    s      = Primitive.unsafeIndex idx_ (2 * q + 1)
    t      = fromIntegral (r - 1) :: Word64
    mask   = negate (Bits.shiftL 0x1 (64 - b))

{-| @(rank i n)@ computes the number of ones up to, but not including the bit at
    index @n@

>>> rank (prepare (fromList [0, maxBound])) 66
Just 2

    The bits are 0-indexed, so @rank i 0@ always returns 0 and @rank i (size i)@
    returns the total number of ones in the bit vector

prop> rank (prepare v) 0 == Just 0
prop> let i = prepare v in rank i (size i) == Just (Primitive.sum (Primitive.map popCount v))

    This returns a valid value wrapped in a `Just` when:

> 0 <= n <= size i

    ... and returns `Nothing` otherwise

prop> let i = prepare v in (0 <= n && n <= size i) || (rank i n == Nothing)
-}
rank :: SuccinctBitVector -> Int -> Maybe Word64
rank i p =
    if 0 <= p && p <= size i
    then Just (unsafeRank i p)
    else Nothing
