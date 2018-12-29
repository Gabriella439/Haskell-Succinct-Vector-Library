{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}

module Succinct.Vector.Index where

import Control.Monad (when)
import Control.DeepSeq (NFData(..))
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.), complement, xor)
import Data.Word (Word8, Word32, Word64)
import Data.Primitive.Types (Prim)
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)
import Prelude hiding ((>>))
import Succinct.Vector.Primitives
import Test.QuickCheck (Arbitrary(..))

import qualified Control.Monad.ST              as ST
import qualified Data.Bits                     as Bits
import qualified Data.Vector
import qualified Data.Vector.Mutable
import qualified Data.Vector.Primitive
import qualified Data.Vector.Primitive.Mutable

-- TODO: Compress the bit vector?
-- TODO: Test with LLVM backend

{-@ measure mlen :: MVector s a -> Int @-}

{-@
assume mutableReplicateMST
    :: n : { n : Int | 0 <= n }
    -> ST s a
    -> ST s ({ v : MVector s a | mlen v == n })
@-}
mutableReplicateMST :: Int -> ST s a -> ST s (MVector s a)
mutableReplicateMST = Data.Vector.Mutable.replicateM
{-# INLINE mutableReplicateMST #-}

{-@
assume Data.Vector.Mutable.unsafeRead
    :: PrimMonad m
    => v : MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < mlen v }
    -> m a
@-}

{-@
assume Data.Vector.Mutable.unsafeWrite
    :: PrimMonad m
    => v : MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < mlen v }
    -> a
    -> m ()
@-}

{-@
assume freezeST
    :: mv : MVector s a -> ST s ({ v : Vector a | vlen v == mlen mv })
@-}
freezeST :: MVector s a -> ST s (Vector a)
freezeST = Data.Vector.freeze
{-# INLINE freezeST #-}

{-@
assume Data.Vector.mapM
    :: Monad m
    => (a -> m b)
    -> i : Vector a
    -> m ({ o : Vector b | vlen o == vlen i })
@-}

{-@
mapMST
    :: (a -> ST s b)
    -> i : Vector a
    -> ST s ({ o : Vector b | vlen o == vlen i })
@-}
mapMST :: (a -> ST s b) -> Vector a -> ST s (Vector b)
mapMST = Data.Vector.mapM
{-# INLINE mapMST #-}

{-@ (>>) :: Word64 -> { n : Int | 0 <= n && n < 64 } -> Word64 @-}
(>>) :: Word64 -> Int -> Word64
(>>) = Bits.unsafeShiftR
{-# INLINE (>>) #-}

{-@ (<<) :: Word64 -> { n : Int | 0 <= n && n < 64 } -> Word64 @-}
(<<) :: Word64 -> Int -> Word64
(<<) = Bits.unsafeShiftL
{-# INLINE (<<) #-}

{-@ assume popCount :: Word64 -> { n : Word64 | 0 <= n && n <= 64 } @-}
popCount :: Word64 -> Word64
popCount w64 = fromIntegral (Bits.popCount w64)
{-# INLINE popCount #-}

{- l1 :: Word64 -> { v : Word64 | v < 4294967296 } -}
l1 :: Word64 -> Word64
l1 w64 = w64 .&. 0x00000000FFFFFFFF
{-# INLINE l1 #-}

{- l2_0 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_0 :: Word64 -> Word64
l2_0 w64 = (w64 .&. 0x000003FF00000000) >> 32
{-# INLINE l2_0 #-}

{- l2_1 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_1 :: Word64 -> Word64
l2_1 w64 = (w64 .&. 0x000FFC0000000000) >> 42
{-# INLINE l2_1 #-}

{- l2_2 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_2 :: Word64 -> Word64
l2_2 w64 = (w64 .&. 0x3FF0000000000000) >> 52
{-# INLINE l2_2 #-}

{-@
l1l2
    :: { l1_   : Word64 | l1_   < 4294967296 }
    -> { l2_0_ : Word64 | l2_0_ < 1024       }
    -> { l2_1_ : Word64 | l2_1_ < 1024       }
    -> { l2_2_ : Word64 | l2_2_ < 1024       }
    -> Word64
@-}
l1l2 :: Word64 -> Word64 -> Word64 -> Word64 -> Word64
l1l2 l1_ l2_0_ l2_1_ l2_2_ =
        l1_
    .|. l2_0_ << 32
    .|. l2_1_ << 42
    .|. l2_2_ << 52

l8 :: Word64
l8 = 0x0101010101010101
{-# INLINE l8 #-}

h8 :: Word64
h8 = ox8080808080808080
  where
    -- Liquid Haskell chokes on numeric literals greater than or equal to
    -- 0x4000000000000000
    --
    -- See: https://github.com/ucsd-progsys/liquid-fixpoint/issues/162
    ox8080808080808080 = 0x2020202020202020
                       + 0x2020202020202020
                       + 0x2020202020202020
                       + 0x2020202020202020
{-# INLINE h8 #-}

lt8 :: Word64 -> Word64 -> Word64
x `lt8` y
    = (((x .|. h8) - (y .&. complement h8)) `xor` x `xor` complement y) .&. h8
{-# INLINE lt8 #-}

le8 :: Word64 -> Word64 -> Word64
x `le8` y
    = (((y .|. h8) - (x .&. complement h8)) `xor` x `xor` y) .&. h8
{-# INLINE le8 #-}

-- `Word64`s always map onto a non-negative integer, but we have to inform
-- Liquid Haskell of that fact
{-@
assume natFromWord64 :: Word64 -> { v : Int | 0 <= v }
@-}
natFromWord64 :: Word64 -> Int
natFromWord64 = fromIntegral
{-# INLINE natFromWord64 #-}

{-@
selectWord64
    :: Word64
    -> { r : Word64 | 0 <= r && r < 64 }
    -> Int
@-}
selectWord64 :: Word64 -> Word64 -> Int
selectWord64 x r = natFromWord64 (b + ((((s3 `le8` (l * l8)) >> 7) * l8) >> 56))
  where
    s0 = x - ((x .&. oxAAAAAAAAAAAAAAAA) >> 1)
    s1 = (s0 .&. 0x3333333333333333) + ((s0 >> 2) .&. 0x3333333333333333)
    s2 = ((s1 + (s1 >> 4)) .&. 0x0F0F0F0F0F0F0F0F) * l8
    b  = ((((s2 `le8` (r * l8)) >> 7) * l8) >> 53) .&. complement 0x7
    {-@ assume b' :: { b : Int | 0 <= b && b < 8 } @-}
    b' = fromIntegral b
    l  = r - (((s2 << 8) >> b') .&. 0xFF)
    s3 = ((0x0 `lt8` (((x >> b' .&. 0xFF) * l8) .&. ox8040201008040201)) >> 0x7) * l8
    -- Liquid Haskell chokes on numeric literals greater than or equal to
    -- 0x4000000000000000
    --
    -- See: https://github.com/ucsd-progsys/liquid-fixpoint/issues/162
    oxAAAAAAAAAAAAAAAA = 0x2222222222222222
                       + 0x3333333333333333
                       + 0x2222222222222222
                       + 0x3333333333333333
    ox8040201008040201 = 0x2010080402010081
                       + 0x2010080402010080
                       + 0x2010080402010080
                       + 0x2010080402010080
{-  IMPLEMENTATION NOTES:

    This is "Algorithm 2" from this paper:

> Vigna, Sebastiano. "Broadword implementation of rank/select queries." Experimental Algorithms. Springer Berlin Heidelberg, 2008. 154-168.

    There was a typo in the original paper.  Line 1 of the original
    "Algorithm 2" has:

> 1  s = (s & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333)

    ... but should have instead been:

> 1  s = (s & 0x3333333333333333) + ((s >> 2) & 0x3333333333333333)
-}
{-# INLINE selectWord64 #-}

{-@
data SuccinctBitVector = SuccinctBitVector
    { vector   :: { vector   : Data.Vector.Primitive.Vector Word64 | 0 <= plen vector }
    , l0s      :: { l0s      : Data.Vector.Primitive.Vector Word64 | plen l0s   = (plen vector / 67108864) + 1 }
    , l1l2s    :: { l1l2s    : Data.Vector.Primitive.Vector Word64 | plen l1l2s = (plen vector / 32      ) + 1 }
    , sample1s :: { sample1s : Vector (Data.Vector.Primitive.Vector Word32) | vlen sample1s = plen l0s }
    , numOnes  :: Word64
    }
@-}

data SuccinctBitVector = SuccinctBitVector
    { vector   :: {-# UNPACK #-} !(Data.Vector.Primitive.Vector Word64)
    , l0s      :: {-# UNPACK #-} !(Data.Vector.Primitive.Vector Word64)
    , l1l2s    :: {-# UNPACK #-} !(Data.Vector.Primitive.Vector Word64)
    , sample1s :: {-# UNPACK #-} !(Vector (Data.Vector.Primitive.Vector Word32))
    , numOnes  :: {-# UNPACK #-} !Word64
    } deriving (Show)

instance NFData SuccinctBitVector where
    rnf (SuccinctBitVector {..}) =
        rnf vector   `seq`
        rnf l0s      `seq`
        rnf l1l2s    `seq`
        rnf sample1s `seq`
        rnf numOnes

instance Arbitrary SuccinctBitVector where
    arbitrary = fmap (prepare . Data.Vector.Primitive.fromList) arbitrary

size :: SuccinctBitVector -> Int
size sbv = Data.Vector.Primitive.length (vector sbv) * 64
{-# INLINE size #-}

-- TODO: Move this to a separate module
data Samples s = Samples
    { samples  :: {-# UNPACK #-} !(Data.Vector.Primitive.Mutable.MVector s Word32)
    , numElems :: {-# UNPACK #-} !Int
    , capacity :: {-# UNPACK #-} !Int
    }

newSamples :: ST s (Samples s)
newSamples = do
    mv <- primitiveNewST 1
    return (Samples mv 0 1)

appendSample :: Word32 -> Samples s -> ST s (Samples s)
appendSample w32 s@(Samples {..}) = do
    Data.Vector.Primitive.Mutable.write samples numElems w32
    let numElems' = numElems + 1
    if numElems' < capacity
    then return (Samples samples numElems' capacity)
    else do
        samples' <- Data.Vector.Primitive.Mutable.grow samples capacity
        return (Samples samples' capacity (2 * capacity))

freezeSamples :: Samples s -> ST s (Data.Vector.Primitive.Vector Word32)
freezeSamples (Samples {..}) =
    primitiveFreezeST
        (Data.Vector.Primitive.Mutable.take numElems samples)

{-| Create a compact index from a `Data.Vector.Primitive.Vector` of `Word64`s
    that supports efficient `rank` and `select` operations
-}
prepare :: Data.Vector.Primitive.Vector Word64 -> SuccinctBitVector
prepare vector = ST.runST (do
    l0sMutable   <- do
        primitiveNewST
            (Data.Vector.Primitive.length vector `div` 67108864 + 1)
    l1l2sMutable <- do
        primitiveNewST
            (Data.Vector.Primitive.length vector `div` 32       + 1)

    let count j =
            if j < Data.Vector.Primitive.length vector
            then popCount (Data.Vector.Primitive.unsafeIndex vector j)
            else 0

    -- TODO: Prove that `loop0` terminates
    let {-@ lazyvar loop0 @-}
        loop0 !i0 !previousCount !currentCount
            | i0 <= Data.Vector.Primitive.length vector = do
                let (p0, q0) = quotRem i0 67108864
                previousCount' <- do
                    if (q0 == 0)
                    then do
                        Data.Vector.Primitive.Mutable.unsafeWrite l0sMutable p0
                            currentCount
                        return currentCount
                    else return previousCount

                let {-@ assume l1_ :: { l1 : Word64 | 0 <= l1 && l1 < 4294967296 }
                    @-}
                    l1_ = currentCount - previousCount'

                -- TODO: Parallelize this addition
                -- TODO: Use more efficient popcount
                let basicBlockCount j0 =
                          count j0
                        + count j1
                        + count j2
                        + count j3
                        + count j4
                        + count j5
                        + count j6
                        + count j7
                      where
                        j1 = j0 + 1
                        j2 = j1 + 1
                        j3 = j2 + 1
                        j4 = j3 + 1
                        j5 = j4 + 1
                        j6 = j5 + 1
                        j7 = j6 + 1
                let i1 = i0 + 8 
                let i2 = i1 + 8 
                let i3 = i2 + 8 
                let i4 = i3 + 8 
                let l2_0_ = basicBlockCount i0
                let l2_1_ = basicBlockCount i1
                let l2_2_ = basicBlockCount i2
                let l2_3_ = basicBlockCount i3

                let l1l2_ = l1l2 l1_ l2_0_ l2_1_ l2_2_
                let p1 = i0 `div` 32
                Data.Vector.Primitive.Mutable.unsafeWrite l1l2sMutable p1 l1l2_

                let currentCount' = currentCount + l2_0_ + l2_1_ + l2_2_ + l2_3_
                loop0 i4 previousCount' currentCount'
            | otherwise = do
                return currentCount
    numOnes <- loop0 0 0 0

    l0s   <- primitiveFreezeST l0sMutable
    l1l2s <- primitiveFreezeST l1l2sMutable

    sample1sMutable <- do
        mutableReplicateMST (Data.Vector.Primitive.length l0s) newSamples

    let {-@ lazyvar loop1 @-}
        loop1 !numOnes !vectorIndex
            | vectorIndex < Data.Vector.Primitive.length vector = do
                let samplesIndex = vectorIndex `div` 67108864 
                let w64 = Data.Vector.Primitive.unsafeIndex vector vectorIndex
                let selectIndex  = (- numOnes) `mod` 8192
                let newOnes      = popCount w64

                if selectIndex < newOnes
                then do
                    let bitIndex = selectWord64 w64 selectIndex
                    samples <- Data.Vector.Mutable.read sample1sMutable
                        samplesIndex
                    let i = vectorIndex * 64 + bitIndex
                          - samplesIndex * 4294967296
                    samples' <- appendSample (fromIntegral i) samples
                    Data.Vector.Mutable.write sample1sMutable samplesIndex
                        samples'
                else return ()

                let numOnes' =
                        if vectorIndex `mod` 67108864 == 67108863
                        then 0
                        else numOnes + newOnes

                loop1 numOnes' (vectorIndex + 1)
            | otherwise = return ()
    loop1 0 0

    sample1s_ <- freezeST sample1sMutable
    sample1s  <- Data.Vector.mapM freezeSamples sample1s_

    return (SuccinctBitVector {..}) )
