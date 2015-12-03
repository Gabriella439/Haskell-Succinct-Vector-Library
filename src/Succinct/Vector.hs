{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Example usage of this module:

>>> import Data.Vector.Unboxed
>>> let v = fromList [maxBound, 0] :: Vector Word64
>>> let sbv = prepare v
>>> index sbv 63
Just True
>>> index sbv 64
Just False
>>> rank sbv 27
Just 27
>>> rank sbv 128
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
    , Position
    , Count
    , index
    , unsafeIndex
    , rank
    , unsafeRank
    ) where

-- TODO: Compress original bit vector

import Control.DeepSeq (NFData(..))
import Data.Bits (Bits, (.|.), (.&.), xor, complement)
import Data.Word (Word16, Word64)
import Prelude hiding ((>>))  -- Use `(>>)` for right bit shift in this module

import qualified Data.Bits           as Bits
import qualified Data.Vector.Generic as Generic
import qualified Data.Vector.Unboxed as Unboxed

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Vector.Unboxed as Unboxed
-- >>> import Test.QuickCheck
-- >>> instance (Unbox a, Arbitrary a) => Arbitrary (Vector a) where arbitrary = fmap fromList arbitrary
-- >>> instance Arbitrary Count where arbitrary = fmap Count arbitrary
-- >>> instance Arbitrary Position where arbitrary = fmap Position arbitrary

{-| Like `index` except that the bit index is not checked

    This will silently fail and return garbage if you supply an invalid index
-}
unsafeIndex :: SuccinctBitVector -> Position -> Bool
unsafeIndex i n = Bits.testBit w8 r
  where
    (q, r) = quotRem (getPosition n) 64
    w8 = Unboxed.unsafeIndex (bits i) q


-- | @(index i n)@ retrieves the bit at the index @n@
index :: SuccinctBitVector -> Position -> Maybe Bool
index i n =
    if 0 <= n && n < size i
    then Just (unsafeIndex i n)
    else Nothing

{-| A bit vector enriched with an index that adds O(1) `rank` and `select`
    queries

    The `SuccinctBitVector` increases the original bit vector's size by 25%
-}
data SuccinctBitVector = SuccinctBitVector
    { size    :: !Position
    -- ^ Size of original bit vector, in bits
    , rank9   :: !(Unboxed.Vector Word64)
    -- ^ Two-level index of cached rank calculations at Word64 boundaries
    , select9 :: !Select9
    -- ^ Primary and secondary inventory used for select calculations
    , bits    :: !(Unboxed.Vector Word64)
    -- ^ Original bit vector
    } deriving (Show)

instance NFData SuccinctBitVector where
    rnf i = i `seq` ()

data Select9 = Select9
    { primary   :: !(Unboxed.Vector Int)
    , secondary :: !(Unboxed.Vector Word64)
    } deriving (Show)

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
h8 = 0x8080808080808080
{-# INLINE h8 #-}

l9 :: Word64
l9 = 0x0040201008040201
{-# INLINE l9 #-}

h9 :: Word64
h9 = 0x4020100804020100
{-# INLINE h9 #-}

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

newtype Position = Position { getPosition :: Int } deriving (Eq, Num, Ord)

instance Show Position where
    show (Position n) = show n

newtype Count = Count { getCount :: Word64 } deriving (Eq, Num, Ord)

instance Show Count where
    show (Count w64) = show w64

{-| Count how many ones there are in the given `Word64`

    This is faster than `Data.Bits.popCount`
-}
popCount :: Word64 -> Count
popCount x0 = Count ((x3 * 0x0101010101010101) >> 56)
  where
    x1 = x0 - ((x0 .&. 0xAAAAAAAAAAAAAAAA) >> 1)
    x2 = (x1 .&. 0x3333333333333333) + ((x1 >> 2) .&. 0x3333333333333333)
    x3 = (x2 + (x2 >> 4)) .&. 0x0F0F0F0F0F0F0F0F
{-  IMPLEMENTATION NOTES:

    This is "Algorithm 1" from this paper:

> Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.
-}
{-# INLINE popCount #-}

unsafeRank64 :: Word64 -> Position -> Count
unsafeRank64 w64 (Position n) =
    popCount (w64 .&. negate (Bits.shiftL 0x1 (64 - n)))
{-  IMPLEMENTATION NOTES:

    Do not use `(<<)`/`Bits.unsafeShiftL` because they do not properly handle
    shifting by 64 bits when `n = 0`
-}
{-# INLINE unsafeRank64 #-}

{-| @(unsafeSelectWord64 w64 n)@ computes the index of the `n`-th one in `w64`
    or return 72s if there is no such one present

    `n` is 0-indexed, meaning that `n = 0` searches for the first one in `w64`

    Similarly, the result is 0-indexed, meaning that a result of 0 points to the
    first bit of `w64`

    Precondition:

> n < 64

    If you violate the precondition this function may silently fail and return
    garbage
-}
unsafeSelect64 :: Word64 -> Count -> (Position, Count)
unsafeSelect64 x (Count r) =
    (Position (fromIntegral (b + ((((s3 `le8` (l * l8)) >> 7) * l8) >> 56))), 1)
  where
    s0 = x - ((x .&. 0xAAAAAAAAAAAAAAAA) >> 1)
    s1 = (s0 .&. 0x3333333333333333) + ((s0 >> 2) .&. 0x3333333333333333)
    s2 = ((s1 + (s1 >> 4)) .&. 0x0F0F0F0F0F0F0F0F) * l8
    b  = ((((s2 `le8` (r * l8)) >> 7) * l8) >> 53) .&. 0xFFFFFFFFFFFFFFF8
    b' = fromIntegral b
    l  = r - (((s2 << 8) >> b') .&. 0xFF)
    s3 = ((0x0 `lt8` (((x >> b' .&. 0xFF) * l8) .&. 0x8040201008040201)) >> 0x7) * l8
{-  IMPLEMENTATION NOTES:

    This is "Algorithm 2" from this paper:

> Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.

    There was a typo in the original paper.  Line 1 of the original
    "Algorithm 2" has:

> 1  s = (s & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333)

    ... but should have instead been:

> 1  s = (s & 0x3333333333333333) + ((s >> 2) & 0x3333333333333333)
-}
{-# INLINE unsafeSelect64 #-}

{-| A non-decreasing list of 7 9-bit counts, packed into one `Word64`

    Bits are 0-indexed and ordered from the least significant (bit #0) to the
    most significant (bit #63):

    Bits #00-08: Word #0
    Bits #09-17: Word #1
    Bits #18-26: Word #2
    Bits #27-35: Word #3
    Bits #36-44: Word #4
    Bits #45-53: Word #5
    Bits #54-62: Word #6
    Bit  #64   : 0
-}
newtype Word9x7 = Word9x7 Word64 deriving (Num)

instance Show Word9x7 where
    show (Word9x7 w64) = show w64

{-| @(unsafeRank9x7 w9x7 i)@ gets the @i@-th 9-bit number stored in @w@ where
    the 1st 9-bit (@i = 1@) is stored in the least significant 9 bits

    Assumptions:

    * @i < 8@

    This always returns `0` for the case where @i = 0@

> unsafeRank9x7 w 0 = 0
-}
unsafeRank9x7 :: Word9x7 -> Position -> Count
unsafeRank9x7 (Word9x7 s) (Position i) =
    Count ((s >> (fromIntegral (t + ((t >> 60) .&. 8)) * 9)) .&. 0x1FF)
  where
    t = i - 1
{-# INLINE unsafeRank9x7 #-}

{-| Create an `SuccinctBitVector` from a `Unboxed.Vector` of bits packed as
    `Word64`s

    You are responsible for padding your data to the next `Word64` boundary
-}
prepare :: Unboxed.Vector Word64 -> SuccinctBitVector
prepare v = SuccinctBitVector
    { size    = Position lengthInBits
    , rank9   = vRank
    , select9 = Select9 v1 v2
    , bits    = v
    }
  where
    lengthInBits = len * 64

    len = Unboxed.length v

    -- TODO: What happens if `len == 0`?
    vRankLen = 2 * (((len - 1) `div` 8) + 1) + 1

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

                count :: Position -> Count
                count i =
                    if i < Position len
                    then popCount (Unboxed.unsafeIndex v (getPosition i))
                    else 0

                r1 =      count i0
                r2 = r1 + count i1
                r3 = r2 + count i2
                r4 = r3 + count i3
                r5 = r4 + count i4
                r6 = r5 + count i5
                r7 = r6 + count i6
                r8 = r7 + count i7

                r' = getCount r1
                 .|. getCount r2 <<  9
                 .|. getCount r3 << 18
                 .|. getCount r4 << 27
                 .|. getCount r5 << 36
                 .|. getCount r6 << 45
                 .|. getCount r7 << 54

        iBegin = Status First 0 0

    -- TODO: Check to see if point-free style interferes with fusion
    v1 :: Unboxed.Vector Int
    v1 =
          flip Unboxed.snoc lengthInBits
        ( Unboxed.map (\(_, i) -> i)
        ( Unboxed.filter (\(j, _) -> j `rem` 512 == 0)
        ( Unboxed.imap (,)
        ( oneIndices 0 (Unboxed.length v)
          v ))))

    oneIndices :: Int -> Int -> Unboxed.Vector Word64 -> Unboxed.Vector Int
    oneIndices i1 i2 v =
          Unboxed.map (\(i, _) -> i)
        ( Unboxed.filter (\(_, b) -> b)
        ( Unboxed.imap (,)
        ( Unboxed.unsafeSlice i1 (i2 - i1)
        ( Unboxed.concatMap (\w64 ->
            Unboxed.generate 64 (Bits.testBit w64) )
          v ))))
    {-# INLINE oneIndices #-}

    count :: Int -> Word64
    count basicBlockIndex =
        let i = basicBlockIndex * 2
        in  if i < Unboxed.length vRank
            then Unboxed.unsafeIndex vRank i
            else fromIntegral (maxBound :: Word16)

    -- TODO: What if the vector is empty?
    locate :: Unboxed.Vector Int -> Int -> Int
    locate v i =
        if i < Unboxed.length v
        then Unboxed.unsafeIndex v i
        else 0

    v2 =
        ( Unboxed.concatMap (\(p, q) ->
            -- TODO: Explain the deviation from the paper here
            let basicBlockBegin = p `div` 512
                basicBlockEnd   = q `div` 512
                numBasicBlocks  = basicBlockEnd - basicBlockBegin
                span            = numBasicBlocks * 2
            in  case () of
                  _ | numBasicBlocks < 1 ->
                        Unboxed.empty
                    | numBasicBlocks < 8 ->
                        Unboxed.generate span (\i ->
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
                        Unboxed.generate span (\i ->
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
                        in  Unboxed.generate span (\i ->
                                let w16 j = fromIntegral (locate ones (4 * i + j))
                                    w64 =    w16 0
                                        .|. (w16 1 << 16)
                                        .|. (w16 2 << 32)
                                        .|. (w16 3 << 48)
                                in  w64 )
                    | numBasicBlocks < 256 ->
                        let ones = oneIndices p q v
                        in  Unboxed.generate span (\i ->
                                let w32 j = fromIntegral (locate ones (2 * i + j))
                                    w64 =    w32 0
                                        .|. (w32 1 << 32)
                                in  w64 )
                    | otherwise ->
                        let ones = oneIndices p q v
                        in  Unboxed.generate span (\i ->
                                let w64 = fromIntegral (p + locate ones i)
                                in  w64 ) )
        ) (Unboxed.zip v1 (Unboxed.drop 1 v1))

{-| Like `rank` except that the bit index is not checked

    This will silently fail and return garbage if you supply an invalid index
-}
unsafeRank :: SuccinctBitVector -> Position -> Count
unsafeRank (SuccinctBitVector _ rank9_ _ bits_) (Position p) =
        Count f
    +   unsafeRank9x7 (Word9x7 s) (Position r)
    +   unsafeRank64 (Unboxed.unsafeIndex bits_ w) (Position b)
  where
    (w, b) = quotRem p 64
    (q, r) = quotRem w 8
    f      = Unboxed.unsafeIndex rank9_ (2 * q    )
    s      = Unboxed.unsafeIndex rank9_ (2 * q + 1)
    t      = fromIntegral (r - 1) :: Word64
    mask   = negate (Bits.shiftL 0x1 (64 - b))

{-| @(rank i n)@ computes the number of ones up to, but not including the bit at
    index @n@

>>> rank (prepare (fromList [0, maxBound])) 66
Just 2

    The bits are 0-indexed, so @rank i 0@ always returns 0 and @rank i (size i)@
    returns the total number of ones in the bit vector

prop> rank (prepare v) 0 == Just 0
prop> let sv = prepare v in fmap getCount (rank sv (size sv)) == Just (Unboxed.sum (Unboxed.map (getCount . popCount) v))

    This returns a valid value wrapped in a `Just` when:

> 0 <= n <= size i

    ... and returns `Nothing` otherwise

prop> let sv = prepare v in (0 <= n && n <= size sv) || (rank sv n == Nothing)
-}
rank :: SuccinctBitVector -> Position -> Maybe Count
rank i p =
    if 0 <= p && p <= size i
    then Just (unsafeRank i p)
    else Nothing
