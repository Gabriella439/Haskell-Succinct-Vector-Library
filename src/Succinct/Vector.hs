{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP                        #-}

#define LIQUID_HASKELL

{-| This module lets you index a vector of bits so that you can efficiently
    navigate those bits using `rank` and `select`:

    * `rank` lets you count how many one or zero bits there are up to a given
      position

    * `select` lets you find the @\'n\'@th one or zero

    Many other operations you might want to perform can be reduced to the
    primitive `rank` and `select` functions.  Think of this module as a building
    block for building higher-level high-performance algorithms.

    This module is based on the paper:

    <http://vigna.di.unimi.it/ftp/papers/Broadword.pdf Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.>

    ... which shows how to implement an efficient index that provides fast O(1)
    `rank` and `select` operations.

    This is not the only possible way to index a bit vector to provide `rank`
    and `select` and there are other implementations that provide varying
    tradeoffs.  I picked this implementation because it is the most efficient
    implementation that provides constant-time `rank` and `select` operations,
    no matter how large the input bit vector is.

    The disadvantage of this implementation is that it requires a substantial
    amount of space for the index (87.5% of the size of the original input bit
    vector).  Other implementations can index the bit vector in a small fraction
    of the space, but at the expense of O(log N) operations, such as this one:

    <https://www.cs.cmu.edu/~dga/papers/zhou-sea2013.pdf Zhou, Dong, David G. Andersen, and Michael Kaminsky. "Space-efficient, high-performance rank and select structures on uncompressed bit sequences." Experimental Algorithms. Springer Berlin Heidelberg, 2013. 151-163.>

    Here is an example of how you would use this module:

>>> import Data.Vector.Unboxed
>>> -- An example 128-bit input vector
>>> let v  = fromList [0x0000000000000001, 0x0000000000000002] :: Vector Word64
>>> -- Build an index from the bit vector
>>> let bv = prepare v

>>> index bv   0  -- The lowest bit of the first `Word64`
Just True
>>> index bv   1  -- The second-lowest bit of the first `Word64`
Just False
>>> index bv  64  -- The lowest bit of the second `Word64`
Just False
>>> index bv  65  -- The second-lowest bit of the second `Word64`
Just True
>>> index bv 129  -- Out-of-bounds `index` fails
Nothing

>>> rank bv   0  -- Count how many ones in the first 0 bits (always returns 0)
Just 0
>>> rank bv   1  -- Count how many ones in the first 1 bits
Just 1
>>> rank bv   2  -- Count how many ones in the first 2 bits
Just 1
>>> rank bv 128  -- Count how many ones in all 128 bits
Just 2
>>> rank bv 129  -- Out-of-bounds `rank` fails
Nothing

>>> select bv 0  -- Find the 0-indexed position of the first one bit
Just 0
>>> select bv 1  -- Find the 0-indexed position of the second one bit
Just 65
>>> select bv 2  -- Out-of-bounds `select` fails
Nothing

-}

module Succinct.Vector (
    -- * Construction
      BitVector
    , prepare
    , index

    -- * Queries
    , Position(..)
    , Count(..)
    , SuccinctBitVector(..)
    , rank
    , select

    -- * Internals
    , BasicBlock(..)
    , IntermediateBlock(..)
    , SuperBlock(..)
    ) where

-- TODO: Compress original bit vector
-- TODO: Carefully examine all `fromIntegral` uses

import Control.DeepSeq (NFData(..))
import Control.Monad (guard, replicateM)
import Data.Bits (Bits, (.|.), (.&.), xor, complement)
import Data.List (sort)
import Data.Word (Word16, Word64)
import Prelude hiding ((>>))  -- Use `(>>)` for right bit shift in this module
import Test.QuickCheck (Arbitrary(..), choose)

import qualified Data.Bits           as Bits
#ifdef LIQUID_HASKELL
import qualified Data.Vector         as Unboxed
#else
import qualified Data.Vector.Unboxed as Unboxed
#endif
import qualified Test.QuickCheck     as QuickCheck

-- $setup
-- >>> import Data.Vector.Unboxed as Unboxed
-- >>> import Test.QuickCheck
-- >>> instance (Unbox a, Arbitrary a) => Arbitrary (Vector a) where arbitrary = fmap fromList arbitrary

{-| Like `index` except that the bit index is not checked

    This will silently fail and return garbage if you supply an invalid index
-}
unsafeIndex :: BitVector -> Position -> Bool
unsafeIndex i n = Bits.testBit w8 r
  where
    (q, r) = quotRem (getPosition n) 64
    w8 = Unboxed.unsafeIndex (bits i) q

{-| A `BitVector` contains the original input vector and you can use
    @(index i n)@ retrieves the bit at index @n@ from the original vector

prop> let bv = prepare (Unboxed.fromList w64s) in index bv n == do r1 <- rank bv n; r2 <- rank bv (n + 1); return (r1 < r2)
-}
index :: BitVector -> Position -> Maybe Bool
index i n =
    if 0 <= n && n < size i
    then Just (unsafeIndex i n)
    else Nothing

{-| A bit vector enriched with an index that adds O(1) `rank` and `select`
    queries

    The `BitVector` increases the original bit vector's size by 87.5%
-}
data BitVector = BitVector
    { rank9   :: !(Unboxed.Vector Word64)
    -- ^ Two-level index of cached rank calculations at Word64 boundaries
    , select9 :: !Select9
    -- ^ Primary and secondary inventory used for select calculations
    , bits    :: !(Unboxed.Vector Word64)
    -- ^ Original bit vector
    } deriving (Show)

instance NFData BitVector where
    rnf i = i `seq` ()

instance Arbitrary BitVector where
    arbitrary = fmap (prepare . Unboxed.fromList) arbitrary

data Select9 = Select9
    { primary_   :: !(Unboxed.Vector Int)
    , secondary_ :: !(Unboxed.Vector Word64)
    } deriving (Show)
{-@
data Select9 = Select9
    { primary_   :: (Unboxed.Vector { v : Int | 0 <= v })
    , secondary_ :: (Unboxed.Vector Word64)
    }
@-}

data Level = First | Second

data Status = Status
                   !Level
    {-# UNPACK #-} !Count
    {-# UNPACK #-} !Position

(>>) :: Bits a => a -> Int -> a
(>>) = Bits.unsafeShiftR
{-# INLINE (>>) #-}

(<<) :: Bits a => a -> Int -> a
(<<) = Bits.unsafeShiftL
{-# INLINE (<<) #-}

l8 :: Word64
l8 = 0x0101010101010101
{-# INLINE l8 #-}

h8 :: Word64
h8 = ox8080808080808080
  where
    ox8080808080808080 = 0x2020202020202020
                       + 0x2020202020202020
                       + 0x2020202020202020
                       + 0x2020202020202020
{-# INLINE h8 #-}

l9 :: Word64
l9 = 0x0040201008040201
{-# INLINE l9 #-}

h9 :: Word64
h9 = ox4020100804020100
  where
    ox4020100804020100 = 0x2010080402010080
                       + 0x2010080402010080
{-# INLINE h9 #-}

l16 :: Word64
l16 = 0x0001000100010001
{-# INLINE l16 #-}

h16 :: Word64
h16 = ox8000800080008000
  where
    ox8000800080008000 = 0x2000200020002000
                       + 0x2000200020002000
                       + 0x2000200020002000
                       + 0x2000200020002000
{-# INLINE h16 #-}

le8 :: Word64 -> Word64 -> Word64
x `le8` y
    = (((y .|. h8) - (x .&. complement h8)) `xor` x `xor` y) .&. h8
{-# INLINE le8 #-}

lt8 :: Word64 -> Word64 -> Word64
x `lt8` y
    = (((x .|. h8) - (y .&. complement h8)) `xor` x `xor` complement y) .&. h8
{-# INLINE lt8 #-}

leu9 :: Word64 -> Word64 -> Word64
x `leu9` y
    =   (     (((y .|. h9) - (x .&. complement h9)) .|. (x `xor` y))
        `xor` (x .&. complement y)
        )
    .&. h9
{-# INLINE leu9 #-}

leu16 :: Word64 -> Word64 -> Word64
x `leu16` y
    =   (     (((y .|. h16) - (x .&. complement h16)) .|. (x `xor` y))
        `xor` (x .&. complement y)
        )
    .&. h16
{-# INLINE leu16 #-}

-- | A 0-indexed bit position
newtype Position = Position { getPosition :: Int } deriving (Eq, Num, Ord)
{-@
data Position = Position { getPosition :: { v : Int | 0 <= v } }
@-}

instance Show Position where
    show (Position n) = show n

-- I assume that `QuickCheck` implemented this correctly :)
{-@
assume arbitraryNonNegative :: QuickCheck.Gen { v : Int | 0 <= v }
@-}
arbitraryNonNegative :: QuickCheck.Gen Int
arbitraryNonNegative = fmap QuickCheck.getNonNegative arbitrary

instance Arbitrary Position where
    arbitrary = fmap Position arbitraryNonNegative

-- | A count of bits
newtype Count = Count { getCount :: Word64 } deriving (Eq, Num, Ord)

instance Show Count where
    show (Count w64) = show w64

instance Arbitrary Count where
    arbitrary = fmap Count arbitrary

-- `Word64`s always map onto a non-negative integer, but we have to inform
-- Liquid Haskell of that fact
{-@
assume natFromWord64 :: Word64 -> { v : Int | 0 <= v }
@-}
natFromWord64 :: Word64 -> Int
natFromWord64 = fromIntegral
{-# INLINE natFromWord64 #-}

{-| Count how many ones there are in the given `Word64`

    This is faster than `Data.Bits.popCount`
-}
popCount :: Word64 -> Count
popCount x0 = Count ((x3 * 0x0101010101010101) >> 56)
  where
    x1 = x0 - ((x0 .&. oxAAAAAAAAAAAAAAAA) >> 1)
    x2 = (x1 .&. 0x3333333333333333) + ((x1 >> 2) .&. 0x3333333333333333)
    x3 = (x2 + (x2 >> 4)) .&. 0x0F0F0F0F0F0F0F0F
    oxAAAAAAAAAAAAAAAA = 0x2222222222222222
                       + 0x3333333333333333
                       + 0x2222222222222222
                       + 0x3333333333333333
{-  IMPLEMENTATION NOTES:

    This is "Algorithm 1" from this paper:

> Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.
-}
{-# INLINE popCount #-}

{-|
-}
class SuccinctBitVector v where
    partialRank   :: v -> Position -> (Count   , Position)
    partialSelect :: v -> Count    -> (Position, Count   )
    size          :: v -> Position

{-| @(rank sbv p)@ computes the number of ones up to, but not including the bit
    at index @p@ (0-indexed)

>>> rank (prepare (fromList [0, maxBound])) 66
Just 2

    The bits are 0-indexed, so @rank sbv 0@ always returns 0 and
    @rank sbv (size sbv)@ returns the total number of ones in the succinct bit
    vector

prop> rank (prepare v) 0 == Just 0
prop> let sbv = prepare v in fmap getCount (rank sbv (size sbv)) == Just (Unboxed.sum (Unboxed.map (getCount . popCount) v))

    This returns a valid value wrapped in a `Just` when @0 <= p <= size sbv@:

prop> let sbv = prepare v in not (0 <= p && p <= size sbv) || (rank sbv p > Nothing)

    ... and returns `Nothing` otherwise:

prop> let sbv = prepare v in (0 <= p && p <= size sbv) || (rank sbv p == Nothing)
-}
rank :: SuccinctBitVector a => a -> Position -> Maybe Count
rank sbv p0 = do
    guard (0 <= p0 && p0 <= size sbv)
    let (c1, p1) = partialRank sbv p0
    guard (p1 == 0)
    return c1

{-| @(select sbv c)@ computes the location of the @\'c\'@th one bit (0-indexed)
-}
select :: SuccinctBitVector a => a -> Count -> Maybe Position
select sbv c0 = do
    n <- rank sbv (size sbv)
    guard (0 <= c0 && c0 < n)
    let (p1, c1) = partialSelect sbv c0
    guard (c1 == 0)
    return p1

instance SuccinctBitVector Word64 where
    partialRank w64 (Position n) = (popCount (w64 .&. ((Bits.shiftL 0x1 n) - 1)), 0)
    {-# INLINE partialRank #-}

    partialSelect x (Count r) =
        (Position (natFromWord64 (b + ((((s3 `le8` (l * l8)) >> 7) * l8) >> 56))), 0)
      where
        s0 = x - ((x .&. oxAAAAAAAAAAAAAAAA) >> 1)
        s1 = (s0 .&. 0x3333333333333333) + ((s0 >> 2) .&. 0x3333333333333333)
        s2 = ((s1 + (s1 >> 4)) .&. 0x0F0F0F0F0F0F0F0F) * l8
        b  = ((((s2 `le8` (r * l8)) >> 7) * l8) >> 53) .&. complement 0x7
        b' = fromIntegral b
        l  = r - (((s2 << 8) >> b') .&. 0xFF)
        s3 = ((0x0 `lt8` (((x >> b' .&. 0xFF) * l8) .&. ox8040201008040201)) >> 0x7) * l8
        oxAAAAAAAAAAAAAAAA = 0x2222222222222222
                           + 0x3333333333333333
                           + 0x2222222222222222
                           + 0x3333333333333333
        ox8040201008040201 = 0x2010080402010081
                           + 0x2010080402010080
                           + 0x2010080402010080
                           + 0x2010080402010080
    {-# INLINE partialSelect #-}
    {-  IMPLEMENTATION NOTES:

        This is "Algorithm 2" from this paper:

    > Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.

        There was a typo in the original paper.  Line 1 of the original
        "Algorithm 2" has:

    > 1  s = (s & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333)

        ... but should have instead been:

    > 1  s = (s & 0x3333333333333333) + ((s >> 2) & 0x3333333333333333)
    -}

    size _ = 64
    {-# INLINE size #-}

{-| A `BasicBlock` caches the ranks of 8 consecutive `Word64`s relative to the
    rank of the first `Word64`.  Each rank requires 9 bits of space since the
    maximum relative rank is @7 * 64 = 448@.  The rank of the first `Word64`
    relative to itself is always 0 so we never need to store it, meaning that we
    can store the remaining 7 ranks in @7 * 9 = 63@ bits laid out like this:

> --           Rank of Word64 #0 omitted since it's always 0
> Bits #00-08: Rank of Word64 #1
> Bits #09-17: Rank of Word64 #2
> Bits #18-26: Rank of Word64 #3
> Bits #27-35: Rank of Word64 #4
> Bits #36-44: Rank of Word64 #5
> Bits #45-53: Rank of Word64 #6
> Bits #54-62: Rank of Word64 #7
> Bit  #63   : 0

    Bits are 0-indexed and ordered from the least significant (bit #0) to the
    most significant (bit #63)
-}
newtype BasicBlock = BasicBlock { getBasicBlock :: Word64 } deriving (Num, Show)

instance Arbitrary BasicBlock where
    arbitrary = do
        r1 <- QuickCheck.choose ( 0, 511)
        r2 <- QuickCheck.choose (r1, 511)
        r3 <- QuickCheck.choose (r2, 511)
        r4 <- QuickCheck.choose (r3, 511)
        r5 <- QuickCheck.choose (r4, 511)
        r6 <- QuickCheck.choose (r5, 511)
        r7 <- QuickCheck.choose (r6, 511)
        return
            (BasicBlock
                (   r1
                .|. r2 <<  9
                .|. r3 << 18
                .|. r4 << 27
                .|. r5 << 36
                .|. r6 << 45
                .|. r7 << 54
                )
            )

instance SuccinctBitVector BasicBlock where
    partialRank (BasicBlock s) (Position i) =
        (Count ((s >> (fromIntegral (t + ((t >> 60) .&. 8)) * 9)) .&. 0x1FF), Position q)
      where
        (p, q) = i `quotRem` 64

        t = p - 1
    {-# INLINE partialRank #-}

    partialSelect (BasicBlock s) (Count r) = (Position (64 * o), Count r')
      where
        o  = natFromWord64 (((((s `leu9` (r * l9)) >> 8) * l9) >> 54) .&. 7)
        r' = r - ((s >> fromIntegral (((o - 1) .&. 7) * 9)) .&. 0x1FF)
    {-# INLINE partialSelect #-}

    size _ = 512
    {-# INLINE size #-}

partialRankLevel0 :: Unboxed.Vector Word64 -> Position -> (Count, Position)
partialRankLevel0 v (Position i) = (Count n, Position q)
  where
    n = Unboxed.unsafeIndex v (p * 2)

    (p, q) = i `quotRem` 512
{-# INLINE partialRankLevel0 #-}

{-| An `IntermediateBlock` caches the ranks of up to 64 consecutive
    `BasicBlock`s relative to the rank of the first `BasicBlock`.  Since each
    `BasicBlock` represents @8 * 64 = 512@ bits worth of data the maximum
    relative rank is @63 * 512 = 32256@ which can be stored in 15 bits, but we
    round up to 16 bits for alignment reasons.  This means that we store four
    ranks per `Word64` for up to 16 `Word64`s, laid out like this:

> Word64 #00 - Bits #00-15: Rank of BasicBlock #00 (Always 0)
> Word64 #00 - Bits #16-31: Rank of BasicBlock #01
> Word64 #00 - Bits #32-47: Rank of BasicBlock #02
> Word64 #00 - Bits #48-63: Rank of BasicBlock #03
> Word64 #01 - Bits #00-15: Rank of BasicBlock #04
> Word64 #01 - Bits #16-31: Rank of BasicBlock #04
> Word64 #01 - Bits #32-47: Rank of BasicBlock #06
> Word64 #01 - Bits #48-63: Rank of BasicBlock #07
> ...
> Word64 #15 - Bits #00-15: Rank of BasicBlock #60
> Word64 #15 - Bits #16-31: Rank of BasicBlock #61
> Word64 #15 - Bits #32-47: Rank of BasicBlock #62
> Word64 #15 - Bits #48-63: Rank of BasicBlock #63

    Bits are 0-indexed and ordered from the least significant (bit #0) to the
    most significant (bit #63)
-}
newtype IntermediateBlock = IntermediateBlock
    { getIntermediateBlock :: Unboxed.Vector Word64
    } deriving (Show)

instance Arbitrary IntermediateBlock where
    arbitrary = do
        n      <- choose (0, 63)
        w16s_0 <- replicateM n (choose (0, 65535))
        let w64s (w16_0:w16_1:w16_2:w16_3:w16s) =
                let w64 =   w16_0
                        .|. w16_1 << 16
                        .|. w16_2 << 32
                        .|. w16_3 << 48
                in  w64:w64s w16s
            w64s [w16_0, w16_1, w16_2] = w64s [w16_0, w16_1, w16_2, 0]
            w64s [w16_0, w16_1]        = w64s [w16_0, w16_1, 0    , 0]
            w64s [w16_0]               = w64s [w16_0, 0    , 0    , 0]
            w64s []                    = []
        return (IntermediateBlock (Unboxed.fromList (w64s (0:sort w16s_0))))

instance SuccinctBitVector IntermediateBlock where
    partialRank (IntermediateBlock w64s) (Position i) = (Count r, Position i')
      where
        (basicBlockIndex, i') = i `quotRem` 512

        (vectorIndex, w16Index) = basicBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r = (w64 >> (w16Index << 4)) .&. 0xFFFF
    {-# INLINE partialRank #-}

    partialSelect (IntermediateBlock w64s) (Count r) = (Position i, Count r')
      where
        basicBlockIndex
            =   natFromWord64
                ( Unboxed.sum
                    ( Unboxed.map
                        (\w -> (((w `leu16` (r * l16)) >> 15) * l16) >> 48)
                        w64s
                    )
                ) - 1

        i = basicBlockIndex << 9

        (vectorIndex, w16Index) = basicBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r' = r - ((w64 >> (w16Index << 4)) .&. 0xFFFF)
    {-# INLINE partialSelect #-}

    size (IntermediateBlock w64s) = Position (512 * Unboxed.length w64s)
    {-# INLINE size #-}

{-| A `SuperBlock` caches the ranks of up to 8 consecutive `IntermediateBlock`s
    relative to the rank of the first `IntermediateBlock`.  Since each
    `IntermediateBlock` represents @8 * 512 = 4096@ bits worth of data the
    maximum relative rank is @7 * 4096 = 28672@ which can be stored in 15 bits,
    but we round up to 16 bits for alignment reasons.  This means that we store
    four ranks per `Word64` for up to 16 `Word64`s, laid out like this:

> Word64 #0 - Bits #00-15: Rank of IntermediateBlock #00 (Always 0)
> Word64 #0 - Bits #16-31: Rank of IntermediateBlock #01
> Word64 #0 - Bits #32-47: Rank of IntermediateBlock #02
> Word64 #0 - Bits #48-63: Rank of IntermediateBlock #03
> Word64 #1 - Bits #00-15: Rank of IntermediateBlock #04
> Word64 #1 - Bits #16-31: Rank of IntermediateBlock #04
> Word64 #1 - Bits #32-47: Rank of IntermediateBlock #06
> Word64 #1 - Bits #48-63: Rank of IntermediateBlock #07

    Bits are 0-indexed and ordered from the least significant (bit #0) to the
    most significant (bit #63)
-}
newtype SuperBlock = SuperBlock
    { getSuperBlock :: Unboxed.Vector Word64
    } deriving (Show)

instance Arbitrary SuperBlock where
    arbitrary = do
        n      <- choose (0, 7)
        w16s_0 <- replicateM n (choose (0, 65535))
        let w64s (w16_0:w16_1:w16_2:w16_3:w16s) =
                let w64 =   w16_0
                        .|. w16_1 << 16
                        .|. w16_2 << 32
                        .|. w16_3 << 48
                in  w64:w64s w16s
            w64s [w16_0, w16_1, w16_2] = w64s [w16_0, w16_1, w16_2, 0]
            w64s [w16_0, w16_1]        = w64s [w16_0, w16_1, 0    , 0]
            w64s [w16_0]               = w64s [w16_0, 0    , 0    , 0]
            w64s []                    = []
        return (SuperBlock (Unboxed.fromList (w64s (0:sort w16s_0))))

instance SuccinctBitVector SuperBlock where
    partialRank (SuperBlock w64s) (Position i) = (Count r, Position i')
      where
        (intermediateBlockIndex, i') = i `quotRem` 4096

        (vectorIndex, w16Index) = intermediateBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r = (w64 >> (w16Index << 4)) .&. 0xFFFF
    {-# INLINE partialRank #-}

    partialSelect (SuperBlock w64s) (Count r) = (Position i, Count r')
      where
        intermediateBlockIndex
            =   natFromWord64
                ( Unboxed.sum
                    ( Unboxed.map
                        (\w -> (((w `leu16` (r * l16)) >> 15) * l16) >> 48)
                        w64s
                    )
                ) - 1

        i = intermediateBlockIndex << 9

        (vectorIndex, w16Index) = intermediateBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r' = r - ((w64 >> (w16Index << 4)) .&. 0xFFFF)
    {-# INLINE partialSelect #-}

    size (SuperBlock w64s) = Position (Unboxed.length w64s * 4096)
    {-# INLINE size #-}

{-| Create an `BitVector` from a `Unboxed.Vector` of bits packed as `Word64`s

    You are responsible for padding your data to the next `Word64` boundary
-}
prepare :: Unboxed.Vector Word64 -> BitVector
prepare v = BitVector
    { rank9   = vRank
    , select9 = Select9 v1 v2
    , bits    = v
    }
  where
    len = Unboxed.length v

    -- TODO: What happens if `len == 0`?
    vRankLen = 2 * (((len + 7) `div` 8) + 1)

    vRank = Unboxed.unfoldrN vRankLen iStep iBegin
      where
        iStep (Status level r i0) = Just (case level of
            First  -> (getCount r , Status Second r       i0)
            Second -> (         r', Status First (r + r8) i8) )
              where
                i1 = i0 + 1
                i2 = i1 + 1
                i3 = i2 + 1
                i4 = i3 + 1
                i5 = i4 + 1
                i6 = i5 + 1
                i7 = i6 + 1
                i8 = i7 + 1

                countBits :: Position -> Count
                countBits i =
                    if i < Position len
                    then popCount (Unboxed.unsafeIndex v (getPosition i))
                    else 0

                r1 =      countBits i0
                r2 = r1 + countBits i1
                r3 = r2 + countBits i2
                r4 = r3 + countBits i3
                r5 = r4 + countBits i4
                r6 = r5 + countBits i5
                r7 = r6 + countBits i6
                r8 = r7 + countBits i7

                r' = getCount r1
                 .|. getCount r2 <<  9
                 .|. getCount r3 << 18
                 .|. getCount r4 << 27
                 .|. getCount r5 << 36
                 .|. getCount r6 << 45
                 .|. getCount r7 << 54

        iBegin = Status First 0 0

    v1 :: Unboxed.Vector Int
    v1 =
          flip Unboxed.snoc (len * 64)
        ( Unboxed.map (\(_, i) -> i)
        ( Unboxed.filter (\(j, _) -> j `rem` 512 == 0)
        ( Unboxed.imap (,)
        ( oneIndices 0 (Unboxed.length v)
          v ))))

    {-@
    oneIndices
        :: Int
        -> Int
        -> Unboxed.Vector Word64
        -> Unboxed.Vector { v : Int | 0 <= v }
    @-}
    oneIndices :: Int -> Int -> Unboxed.Vector Word64 -> Unboxed.Vector Int
    oneIndices i1 i2 vector =
          Unboxed.map (\(i, _) -> i)
        ( Unboxed.filter (\(_, b) -> b)
        ( Unboxed.imap (,)
        ( Unboxed.unsafeSlice i1 (i2 - i1)
        ( Unboxed.concatMap (\w64 ->
            Unboxed.generate 64 (Bits.testBit w64) )
          vector ))))
    {-# INLINE oneIndices #-}

    count :: Int -> Word64
    count basicBlockIndex =
        let i = basicBlockIndex * 2
        in  if i < Unboxed.length vRank
            then Unboxed.unsafeIndex vRank i
            else fromIntegral (maxBound :: Word16)

    locate :: Unboxed.Vector Int -> Int -> Int
    locate vector i =
        if i < Unboxed.length vector
        then Unboxed.unsafeIndex vector i
        else 0

    v2 =
        ( Unboxed.concatMap (\(p, q) ->
            -- TODO: Explain the deviation from the paper here
            let basicBlockBegin = p `quot` 512
                basicBlockEnd   = q `quot` 512
                numBasicBlocks  = basicBlockEnd - basicBlockBegin
                s               = numBasicBlocks * 2
            in  case () of
                  _ | numBasicBlocks < 1 ->
                        Unboxed.empty
                    | numBasicBlocks < 8 ->
                        Unboxed.generate s (\i ->
                                 if  i < 2
                            then let w16 j = count (basicBlockBegin + 4 * i + j)
                                           - count basicBlockBegin
                                     w64   =  w16 0
                                         .|. (w16 1 << 16)
                                         .|. (w16 2 << 32)
                                         .|. (w16 3 << 48)
                                 in  w64
                            else 0 )
                    | numBasicBlocks < 64 ->
                        Unboxed.generate s (\i ->
                                 if  i < 2
                            then let w16 j = count (basicBlockBegin + 8 * (4 * i + j))
                                           - count basicBlockBegin
                                     w64   =  w16 0
                                         .|. (w16 1 << 16)
                                         .|. (w16 2 << 32)
                                         .|. (w16 3 << 48)
                                 in  w64
                            else if  i < 18
                            then let w16 j = count (basicBlockBegin + 4 * (i - 2) + j)
                                           - count basicBlockBegin
                                     w64   =  w16 0
                                         .|. (w16 1 << 16)
                                         .|. (w16 2 << 32)
                                         .|. (w16 3 << 48)
                                 in  w64
                            else 0 )
                    | numBasicBlocks < 128 ->
                        let ones = oneIndices p q v
                        in  Unboxed.generate s (\i ->
                                let w16 j = fromIntegral (locate ones (4 * i + j))
                                    w64 =    w16 0
                                        .|. (w16 1 << 16)
                                        .|. (w16 2 << 32)
                                        .|. (w16 3 << 48)
                                in  w64 )
                    | numBasicBlocks < 256 ->
                        let ones = oneIndices p q v
                        in  Unboxed.generate s (\i ->
                                let w32 j = fromIntegral (locate ones (2 * i + j))
                                    w64 =    w32 0
                                        .|. (w32 1 << 32)
                                in  w64 )
                    | otherwise ->
                        let ones = oneIndices p q v
                        in  Unboxed.generate s (\i ->
                                let w64 = fromIntegral (p + locate ones i)
                                in  w64 ) )
        ) (Unboxed.zip v1 (Unboxed.drop 1 v1))

instance SuccinctBitVector BitVector where
    partialRank (BitVector rank9_ _ bits_) p0 = (c1 + c2 + c3, p3)
      where
        (c1, p1) = partialRankLevel0 rank9_     p0
        (c2, p2) = partialRank       basicBlock p1
        (c3, p3) = partialRank       w64        p2
        basicBlock = BasicBlock (Unboxed.unsafeIndex rank9_ (2 * (getPosition p0 `quot` 512) + 1))
        w64        = Unboxed.unsafeIndex bits_ (getPosition p0 `quot` 64)

    partialSelect (BitVector rank9_ (Select9 primary_ secondary_) bits_) r =
        let i               = getCount r `quot` 512
            p               = Unboxed.unsafeIndex primary_ (fromIntegral i)
            q               = Unboxed.unsafeIndex primary_ (fromIntegral i + 1)
            -- TODO: Use `quot` instead when this pull request is merged:
            -- https://github.com/ucsd-progsys/liquidhaskell/pull/533
            (basicBlockBegin, _) = p `quotRem` 512
            basicBlockEnd   = q `quot` 512
            p1              = Position (basicBlockBegin * 512)
            c1              = r - Count (Unboxed.unsafeIndex rank9_ (basicBlockBegin * 2))
            numBasicBlocks  = basicBlockEnd - basicBlockBegin
            secondaryBegin  = basicBlockBegin * 2
        in  case () of
              _ | numBasicBlocks < 2 ->
                    let basicBlockIndex = getPosition p1 `quot` 512
                        basicBlock      = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64             = Unboxed.unsafeIndex bits_ (getPosition (p1 + p2) `quot` 64)
                        (p2, c2) = partialSelect basicBlock c1
                        (p3, c3) = partialSelect w64        c2
                    in  (p1 + p2 + p3, c3)
                | numBasicBlocks < 8 ->
                    let intermediateBlock = IntermediateBlock (Unboxed.unsafeSlice secondaryBegin 2 secondary_)
                        basicBlockIndex   = getPosition (p1 + p2     ) `quot` 512
                        w64Index          = getPosition (p1 + p2 + p3) `quot`  64
                        basicBlock        = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64               = Unboxed.unsafeIndex bits_ w64Index
                        (p2, c2) = partialSelect intermediateBlock c1
                        (p3, c3) = partialSelect basicBlock        c2
                        (p4, c4) = partialSelect w64               c3
                    in  (p1 + p2 + p3 + p4, c4)
                | numBasicBlocks < 64 ->
                    let superBlock        = SuperBlock (Unboxed.unsafeSlice secondaryBegin 2 secondary_)
                        intermediateBlock = IntermediateBlock (Unboxed.unsafeSlice (secondaryBegin + 2) (min (2 * numBasicBlocks) 18 - 2) secondary_)
                        basicBlockIndex   = getPosition (p1 + p2 + p3     ) `quot` 512
                        w64Index          = getPosition (p1 + p2 + p3 + p4) `quot` 64
                        basicBlock        = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64               = Unboxed.unsafeIndex bits_ w64Index
                        (p2, c2) = partialSelect superBlock        c1
                        (p3, c3) = partialSelect intermediateBlock c2
                        (p4, c4) = partialSelect basicBlock        c3
                        (p5, c5) = partialSelect w64               c4
                    in  (p1 + p2 + p3 + p4 + p5, c5)
                | numBasicBlocks < 128 ->
                    let (vectorIndex, w16Index) = getPosition p1 `quotRem` 4
                        w64 = Unboxed.unsafeIndex secondary_ (secondaryBegin + vectorIndex)
                        p2  = Position (natFromWord64 ((w64 >> (w16Index << 4)) .&. 0xFFFF))
                    in  (p1 + p2, 1)
                | numBasicBlocks < 256 ->
                    let (vectorIndex, w32Index) = getPosition p1 `quotRem` 2
                        w64 = Unboxed.unsafeIndex secondary_ (secondaryBegin + vectorIndex)
                        p2  = Position (natFromWord64 ((w64 >> (w32Index << 5)) .&. 0xFFFFFFFF))
                    in  (p1 + p2, 1)
                | otherwise ->
                    let p2 = Position (natFromWord64 (Unboxed.unsafeIndex secondary_ (getPosition p1)))
                    in  (p2, 1)

    size bv = Position (Unboxed.length (bits bv) * 64)
    {-# INLINE size #-}

{-@
assume Unboxed.imap
    :: ({ v : Int | 0 <= v } -> a -> b) -> Unboxed.Vector a -> Unboxed.Vector b
@-}
