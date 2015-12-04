{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Example usage of this module:

>>> import Data.Vector.Unboxed
>>> let v = fromList [maxBound, 0] :: Vector Word64
>>> let sbv = prepare v
>>> index sbv 63
Just True
>>> index sbv 64
Just False
>>> safeRank sbv 27
Just 27
>>> safeRank sbv 128
Just 64

    This module is based on the paper "Broadword Implementation of Rank/Select
    Queries":

    <http://vigna.di.unimi.it/ftp/papers/Broadword.pdf>
-}

module Succinct.Vector (
    -- * Construction
      BitVector
    , prepare

    -- * Queries
    , Position(..)
    , Count(..)
    , SuccinctBitVector(..)
    , index
    , safeRank
    ) where

-- TODO: Compress original bit vector
-- TODO: Carefully examine all `fromIntegral` uses

import Control.DeepSeq (NFData(..))
import Data.Bits (Bits, (.|.), (.&.), xor, complement)
import Data.Word (Word16, Word64)
import Prelude hiding ((>>))  -- Use `(>>)` for right bit shift in this module

import qualified Data.Bits           as Bits
import qualified Data.Vector.Unboxed as Unboxed
import qualified Numeric

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
unsafeIndex :: BitVector -> Position -> Bool
unsafeIndex i n = Bits.testBit w8 r
  where
    (q, r) = quotRem (getPosition n) 64
    w8 = Unboxed.unsafeIndex (bits i) q


-- | @(index i n)@ retrieves the bit at the index @n@
index :: BitVector -> Position -> Maybe Bool
index i n =
    if 0 <= n && n < size i
    then Just (unsafeIndex i n)
    else Nothing

{-| A bit vector enriched with an index that adds O(1) `rank` and `select`
    queries

    The `BitVector` increases the original bit vector's size by 25%
-}
data BitVector = BitVector
    { size    :: !Position
    -- ^ Size of original bit vector, in bits
    , rank9   :: !(Unboxed.Vector Word64)
    -- ^ Two-level index of cached rank calculations at Word64 boundaries
    , select9 :: !Select9
    -- ^ Primary and secondary inventory used for select calculations
    , bits    :: !(Unboxed.Vector Word64)
    -- ^ Original bit vector
    } deriving (Show)

instance NFData BitVector where
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

l16 :: Word64
l16 = 0x0001000100010001
{-# INLINE l16 #-}

h16 :: Word64
h16 = 0x8000800080008000
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

class SuccinctBitVector v where
    rank   :: v -> Position -> (Count   , Position)
    select :: v -> Count    -> (Position, Count   )

instance SuccinctBitVector Word64 where
    rank w64 (Position n) =
        (popCount (w64 .&. ((0x1 << n) - 1)), 0)
    {-# INLINE rank #-}

    select x (Count r) =
        (Position (fromIntegral (b + ((((s3 `le8` (l * l8)) >> 7) * l8) >> 56))), 0)
      where
        s0 = x - ((x .&. 0xAAAAAAAAAAAAAAAA) >> 1)
        s1 = (s0 .&. 0x3333333333333333) + ((s0 >> 2) .&. 0x3333333333333333)
        s2 = ((s1 + (s1 >> 4)) .&. 0x0F0F0F0F0F0F0F0F) * l8
        b  = ((((s2 `le8` (r * l8)) >> 7) * l8) >> 53) .&. 0xFFFFFFFFFFFFFFF8
        b' = fromIntegral b
        l  = r - (((s2 << 8) >> b') .&. 0xFF)
        s3 = ((0x0 `lt8` (((x >> b' .&. 0xFF) * l8) .&. 0x8040201008040201)) >> 0x7) * l8
    {-# INLINE select #-}
    {-  IMPLEMENTATION NOTES:

        This is "Algorithm 2" from this paper:

    > Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.

        There was a typo in the original paper.  Line 1 of the original
        "Algorithm 2" has:

    > 1  s = (s & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333)

        ... but should have instead been:

    > 1  s = (s & 0x3333333333333333) + ((s >> 2) & 0x3333333333333333)
    -}

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
newtype BasicBlock = BasicBlock Word64 deriving (Num, Show)

instance SuccinctBitVector BasicBlock where
    rank (BasicBlock s) (Position i) =
        (Count ((s >> (fromIntegral (t + ((t >> 60) .&. 8)) * 9)) .&. 0x1FF), Position q)
      where
        (p, q) = i `quotRem` 64

        t = p - 1
    {-# INLINE rank #-}

    select (BasicBlock s) (Count r) = (Position (64 * o), Count r')
      where
        o  = fromIntegral (((((s `leu9` (r * l9)) >> 8) * l9) >> 54) .&. 7)
        r' = r - ((s >> fromIntegral (((o - 1) .&. 7) * 9)) .&. 0x1FF)
    {-# INLINE select #-}

unsafeRankLevel0 :: Unboxed.Vector Word64 -> Position -> (Count, Position)
unsafeRankLevel0 v (Position i) = (Count n, Position q)
  where
    n = Unboxed.unsafeIndex v (p * 2)

    (p, q) = i `quotRem` 512
{-# INLINE unsafeRankLevel0 #-}

newtype IntermediateBlock = IntermediateBlock
    { getIntermediateBlock :: Unboxed.Vector Word64
    } deriving (Show)

instance SuccinctBitVector IntermediateBlock where
    rank (IntermediateBlock w64s) (Position i) = (Count r, Position i')
      where
        (basicBlockIndex, i') = i `quotRem` 512

        (vectorIndex, w16Index) = basicBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r = (w64 >> (w16Index << 4)) .&. 0xFFFF
    {-# INLINE rank #-}

    select (IntermediateBlock w64s) (Count r) = (Position i, Count r')
      where
        basicBlockIndex
            =   fromIntegral
            (   ( Unboxed.sum
                    ( Unboxed.map
                        (\w64 -> (((w64 `leu16` (r * l16)) >> 15) * l16) >> 48)
                        w64s
                    )
                *   l16
                )
            >>  48
            ) - 1

        i = basicBlockIndex << 9

        (vectorIndex, w16Index) = basicBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r' = r - ((w64 >> (w16Index << 4)) .&. 0xFFFF)
    {-# INLINE select #-}

newtype SuperBlock = SuperBlock
    { getSuperBlock :: Unboxed.Vector Word64
    } deriving (Show)

instance SuccinctBitVector SuperBlock where
    rank (SuperBlock w64s) (Position i) = (Count r, Position i')
      where
        (intermediateBlockIndex, i') = i `quotRem` 4096

        (vectorIndex, w16Index) = intermediateBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r = (w64 >> (w16Index << 4)) .&. 0xFFFF
    {-# INLINE rank #-}

    select (SuperBlock w64s) (Count r) = (Position i, Count r')
      where
        intermediateBlockIndex
            =   fromIntegral
            (   ( Unboxed.sum
                    ( Unboxed.map
                        (\w64 -> (((w64 `leu16` (r * l16)) >> 15) * l16) >> 48)
                        w64s
                    )
                *   l16
                )
            >>  48
            ) - 1

        i = intermediateBlockIndex << 9

        (vectorIndex, w16Index) = intermediateBlockIndex `quotRem` 4
        
        w64 = Unboxed.unsafeIndex w64s vectorIndex

        r' = r - ((w64 >> (w16Index << 4)) .&. 0xFFFF)
    {-# INLINE select #-}

{-| Create an `BitVector` from a `Unboxed.Vector` of bits packed as `Word64`s

    You are responsible for padding your data to the next `Word64` boundary
-}
prepare :: Unboxed.Vector Word64 -> BitVector
prepare v = BitVector
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

    v1 :: Unboxed.Vector Int
    v1 =
          flip Unboxed.snoc lengthInBits
        ( Unboxed.map (\(_, i) -> i)
        ( Unboxed.filter (\(j, _) -> j `rem` 512 == 0)
        ( Unboxed.imap (,)
        ( oneIndices 0 (Unboxed.length v)
          v ))))

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
    rank (BitVector _ rank9_ _ bits_) p0 = (c1 + c2 + c3, p3)
      where
        (c1, p1) = unsafeRankLevel0 rank9_     p0
        (c2, p2) = rank             basicBlock p1
        (c3, p3) = rank             w64        p2
        basicBlock = BasicBlock (Unboxed.unsafeIndex rank9_ (2 * (getPosition p0 `quot` 512) + 1))
        w64        = Unboxed.unsafeIndex bits_ (getPosition p0 `quot` 64)

    select (BitVector _ rank9_ (Select9 primary_ secondary_) bits_) r =
        let i               = getCount r `quot` 512
            p               = Unboxed.unsafeIndex primary_ (fromIntegral i)
            q               = Unboxed.unsafeIndex primary_ (fromIntegral i + 1)
            basicBlockBegin = p `quot` 512
            basicBlockEnd   = q `quot` 512
            p1              = Position (basicBlockBegin * 512)
            c1              = r - Count (Unboxed.unsafeIndex rank9_ (basicBlockBegin * 2))
            numBasicBlocks  = basicBlockEnd - basicBlockBegin
            span            = 2 * numBasicBlocks
            secondaryBegin  = basicBlockBegin * 2
        in  case () of
              _ | numBasicBlocks < 2 ->
                    let basicBlockIndex = getPosition p1 `quot` 512
                        basicBlock      = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64             = Unboxed.unsafeIndex bits_ (getPosition (p1 + p2) `quot` 64)
                        (p2, c2) = select basicBlock c1
                        (p3, c3) = select w64        c2
                    in  (p1 + p2 + p3, c3)
                | numBasicBlocks < 8 ->
                    let intermediateBlock = IntermediateBlock (Unboxed.unsafeSlice secondaryBegin 2 secondary_)
                        basicBlockIndex   = getPosition (p1 + p2     ) `quot` 512
                        w64Index          = getPosition (p1 + p2 + p3) `quot`  64
                        basicBlock        = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64               = Unboxed.unsafeIndex bits_ w64Index
                        (p2, c2) = select intermediateBlock c1
                        (p3, c3) = select basicBlock        c2
                        (p4, c4) = select w64               c3
                    in  (p1 + p2 + p3 + p4, c4)
                | numBasicBlocks < 64 ->
                    let superBlock        = SuperBlock (Unboxed.unsafeSlice secondaryBegin 2 secondary_)
                        intermediateBlock = IntermediateBlock (Unboxed.unsafeSlice (secondaryBegin + 2) (min span 18 - 2) secondary_)
                        basicBlockIndex   = getPosition (p1 + p2 + p3     ) `quot` 512
                        w64Index          = getPosition (p1 + p2 + p3 + p4) `quot` 64
                        basicBlock        = BasicBlock (Unboxed.unsafeIndex rank9_ (basicBlockIndex * 2 + 1))
                        w64               = Unboxed.unsafeIndex bits_ w64Index
                        (p2, c2) = select superBlock        c1
                        (p3, c3) = select intermediateBlock c2
                        (p4, c4) = select basicBlock        c3
                        (p5, c5) = select w64               c4
                    in  (p1 + p2 + p3 + p4 + p5, c5)
                | numBasicBlocks < 128 ->
                    let (vectorIndex, w16Index) = getPosition p1 `quotRem` 4
                        w64 = Unboxed.unsafeIndex secondary_ (secondaryBegin + vectorIndex)
                        p2  = Position (fromIntegral ((w64 >> (w16Index << 4)) .&. 0xFFFF))
                    in  (p1 + p2, 1)
                | numBasicBlocks < 256 ->
                    let (vectorIndex, w32Index) = getPosition p1 `quotRem` 2
                        w64 = Unboxed.unsafeIndex secondary_ (secondaryBegin + vectorIndex)
                        p2  = Position (fromIntegral ((w64 >> (w32Index << 5)) .&. 0xFFFFFFFF))
                    in  (p1 + p2, 1)
                | otherwise ->
                    let p2 = Position (fromIntegral (Unboxed.unsafeIndex secondary_ (getPosition p1)))
                    in  (p2, 1)

{-| @(rank i n)@ computes the number of ones up to, but not including the bit at
    index @n@

>>> rank (prepare (fromList [0, maxBound])) 66
Just 2

    The bits are 0-indexed, so @rank i 0@ always returns 0 and @rank i (size i)@
    returns the total number of ones in the bit vector

prop> safeRank (prepare v) 0 == Just 0
prop> let sv = prepare v in fmap getCount (safeRank sv (size sv)) == Just (Unboxed.sum (Unboxed.map (getCount . popCount) v))

    This returns a valid value wrapped in a `Just` when:

> 0 <= n <= size i

    ... and returns `Nothing` otherwise

prop> let sv = prepare v in (0 <= n && n <= size sv) || (safeRank sv n == Nothing)
-}
safeRank :: BitVector -> Position -> Maybe (Count, Position)
safeRank i p =
    if 0 <= p && p <= size i
    then Just (rank i p)
    else Nothing
