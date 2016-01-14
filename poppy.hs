{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}

{-@ LIQUID "--real" @-}

-- module Succinct.Vector where

import Control.Monad (when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.), complement, xor)
import Data.Word (Word8, Word32, Word64)
import Data.Primitive.Types (Prim(..))
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)
import Prelude hiding ((>>))

import qualified Control.Monad.ST              as ST
import qualified Data.Bits                     as Bits
import qualified Data.Vector                   as Vector
import qualified Data.Vector.Generic           as Generic
import qualified Data.Vector.Mutable
import qualified Data.Vector.Mutable           as Vector
import qualified Data.Vector.Primitive
import qualified Data.Vector.Primitive         as Primitive
import qualified Data.Vector.Primitive.Mutable
import qualified Data.Vector.Primitive.Mutable as Primitive

-- TODO: Use `Primitive.unsafeWrite` instead of `Primitive.write`
-- TODO: Compress the bit vector?
-- TODO: Test with LLVM backend

{-@ measure plen :: Primitive.Vector a -> Int @-}

{-@
assume Data.Vector.Primitive.length
    :: Prim a => v : Primitive.Vector a -> { n : Int | 0 <= n && n = plen v }
@-}

{-@
Primitive.unsafeIndex
    :: Prim a
    => v : Primitive.Vector a
    -> { n : Int | 0 <= n && n < plen v }
    -> a
@-}

{-@
assume Primitive.unsafeSlice
    :: Prim a
    => n : { n : Int | 0 <= n }
    -> l : { l : Int | 0 <= l }
    -> i : { i : Primitive.Vector a | n + l <= plen i }
    -> { o : Primitive.Vector a | plen o = l }
@-}

{-@ measure pmlen :: Primitive.MVector s a -> Int @-}

{-@
assume Primitive.unsafeWrite
    :: (PrimMonad m, Prim a)
    => v : Primitive.MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < pmlen v }
    -> a
    -> m ()
@-}

{-@
assume primitiveNewST
    :: Prim a
    => n : Int -> ST s ({ v : Primitive.MVector s a | pmlen v == n })
@-}
primitiveNewST :: Prim a => Int -> ST s (Primitive.MVector s a)
primitiveNewST = Primitive.new
{-# INLINE primitiveNewST #-}

{-@
assume primitiveFreezeST
    :: mv : Primitive.MVector s a
    -> ST s ({ v : Primitive.Vector a | plen v == pmlen mv })
@-}
primitiveFreezeST
    :: Prim a => Primitive.MVector s a -> ST s (Primitive.Vector a)
primitiveFreezeST = Primitive.freeze
{-# INLINE primitiveFreezeST #-}

{-@ measure mlen :: MVector (PrimState m) a -> Int @-}

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
assume Vector.unsafeRead
    :: PrimMonad m
    => v : MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < mlen v }
    -> m a
@-}

{-@
assume Vector.unsafeWrite
    :: PrimMonad m
    => v : MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < mlen v }
    -> a
    -> m ()
@-}

{-@
assume freezeST
    :: mv : MVector s a
    -> ST s ({ v : Vector a | vlen v == mlen mv })
@-}
freezeST :: MVector s a -> ST s (Vector a)
freezeST = Vector.freeze
{-# INLINE freezeST #-}

{-@
assume Vector.mapM
    :: Monad m
    => (a -> m b)
    -> i : Vector a
    -> m ({ o : Vector b | vlen o == vlen i })
@-}

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

{- l2_0 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_0 :: Word64 -> Word64
l2_0 w64 = (w64 .&. 0x000003FF00000000) >> 32

{- l2_1 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_1 :: Word64 -> Word64
l2_1 w64 = (w64 .&. 0x000FFC0000000000) >> 42

{- l2_2 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_2 :: Word64 -> Word64
l2_2 w64 = (w64 .&. 0x3FF0000000000000) >> 52

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
    { vector   :: { vector   : Primitive.Vector Word64 | 0 <= plen vector }
    , l0s      :: { l0s      : Primitive.Vector Word64 | plen l0s      = (plen vector / 67108864) + 1 }
    , l1l2s    :: { l1l2s    : Primitive.Vector Word64 | plen l1l2s    = (plen vector / 32      ) + 1 }
    , sample1s :: { sample1s : Vector (Primitive.Vector Word32) | vlen sample1s = plen l0s }
    , numOnes  :: Word64
    }
@-}

data SuccinctBitVector = SuccinctBitVector
    { vector   :: {-# UNPACK #-} !(Primitive.Vector Word64)
    , l0s      :: {-# UNPACK #-} !(Primitive.Vector Word64)
    , l1l2s    :: {-# UNPACK #-} !(Primitive.Vector Word64)
    , sample1s :: {-# UNPACK #-} !(Vector (Primitive.Vector Word32))
    , numOnes  :: {-# UNPACK #-} !Word64
    } deriving (Show)

size :: SuccinctBitVector -> Int
size sbv = Data.Vector.Primitive.length (vector sbv) * 64

-- TODO: Move this to a separate module
data Samples s = Samples
    { samples  :: {-# UNPACK #-} !(Primitive.MVector s Word32)
    , numElems :: {-# UNPACK #-} !Int
    , capacity :: {-# UNPACK #-} !Int
    }

newSamples :: ST s (Samples s)
newSamples = do
    mv <- primitiveNewST 1
    return (Samples mv 0 1)

appendSample :: Word32 -> Samples s -> ST s (Samples s)
appendSample w32 s@(Samples {..}) = do
    Primitive.write samples numElems w32
    let numElems' = numElems + 1
    if numElems' < capacity
    then return (Samples samples numElems' capacity)
    else do
        samples' <- Primitive.grow samples capacity
        return (Samples samples' capacity (2 * capacity))

freezeSamples :: Samples s -> ST s (Primitive.Vector Word32)
freezeSamples (Samples {..}) =
    primitiveFreezeST (Data.Vector.Primitive.Mutable.take numElems samples)

prepare :: Primitive.Vector Word64 -> SuccinctBitVector
prepare vector = ST.runST (do
    l0sMutable   <- do
        primitiveNewST (Data.Vector.Primitive.length vector `div` 67108864 + 1)
    l1l2sMutable <- do
        primitiveNewST (Data.Vector.Primitive.length vector `div` 32       + 1)

    let count j =
            if j < Data.Vector.Primitive.length vector
            then popCount (Primitive.unsafeIndex vector j)
            else 0

    -- TODO: Prove that `loop0` terminates
    let {-@ Lazy loop0 @-}
        loop0 !i0 !previousCount !currentCount
            | i0 <= Data.Vector.Primitive.length vector = do
                let (p0, q0) = quotRem i0 67108864
                previousCount' <- do
                    if (q0 == 0)
                    then do
                        Primitive.write l0sMutable p0 currentCount
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
                let (p1, _) = quotRem i0 32
                Primitive.write l1l2sMutable p1 l1l2_

                let currentCount' = currentCount + l2_0_ + l2_1_ + l2_2_ + l2_3_
                loop0 i4 previousCount' currentCount'
            | otherwise = return currentCount
    numOnes <- loop0 0 0 0

    l0s   <- primitiveFreezeST l0sMutable
    l1l2s <- primitiveFreezeST l1l2sMutable

    sample1sMutable <- do
        mutableReplicateMST (Data.Vector.Primitive.length l0s) newSamples

    let {-@ Lazy loop1 @-}
        loop1 !numOnes !vectorIndex
            | vectorIndex < Data.Vector.Primitive.length vector = do
                let samplesIndex = vectorIndex `div` 67108864 
                let w64          = Primitive.unsafeIndex vector vectorIndex
                let selectIndex  = (- numOnes) `mod` 8192
                let newOnes      = popCount w64

                if selectIndex < newOnes
                then do
                    let bitIndex = selectWord64 w64 selectIndex
                    samples <- Vector.read sample1sMutable samplesIndex
                    let i = vectorIndex * 64 + bitIndex
                          - samplesIndex * 4294967296
                    samples' <- appendSample (fromIntegral i) samples
                    Vector.write sample1sMutable samplesIndex samples'
                else return ()

                let numOnes' =
                        if vectorIndex `mod` 67108864 == 67108863
                        then -1
                        else numOnes + newOnes

                loop1 numOnes' (vectorIndex + 1)
            | otherwise = return ()
    loop1 0 0

    sample1s_ <- freezeST sample1sMutable
    sample1s  <- Vector.mapM freezeSamples sample1s_

    return (SuccinctBitVector {..}) )

main :: IO ()
main = prepare (Primitive.enumFromN 0 10000000) `seq` return ()

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

    c0   = Primitive.unsafeIndex l0s   p1

    l1l2 = Primitive.unsafeIndex l1l2s p2

    c1   = l1 l1l2

    c2   = case p3 of
        0 -> 0
        1 -> l2_0 l1l2
        2 -> l2_0 l1l2 + l2_1 l1l2
        _ -> l2_0 l1l2 + l2_1 l1l2 + l2_2 l1l2

    c3 =
        Primitive.sum
            (Primitive.map popCount
                (Data.Vector.Primitive.unsafeSlice
                    (((p0 - q2) + p3 * 512) `div` 64)
                    p4
                    vector ) )

{-@
search
    :: (Prim e, Ord a)
    => x  : a
    -> f  : (e -> a)
    -> v  : Primitive.Vector e
    -> lo : { lo : Int | 0  <= lo && lo <  plen v }
    -> hi : { hi : Int | lo <  hi && hi <= plen v }
    -> Int
    / [hi - lo]
@-}
search
    :: (Ord a, Prim e)
    => a -> (e -> a) -> Primitive.Vector e -> Int -> Int -> Int
search x f v lo hi = do
    let mid = lo + (hi - lo) `div` 2
    if hi == lo + 1
    then lo
    else do
        let x' = f (Primitive.unsafeIndex v mid)
        if x < x'
        then search x f v lo  mid
        else search x f v mid hi

-- unsafeSelect :: SuccinctBitVector -> Word64 -> Int
{-
unsafeSelect (SuccinctBitVector {..}) y0 = (pMin, pMax)
  where
    l0Index = search y0 id l0s 0 (Data.Vector.Primitive.length l0s)
    l0      = Primitive.unsafeIndex l0s l0Index
    y1      = y0 - l0
    pMin    =
        Primitive.unsafeIndex
            (Vector.unsafeIndex sample1s l0Index)
            (fromIntegral ((y1 `div` 8192) * 8192    ))
    pMax    =
        Primitive.unsafeIndex
            (Vector.unsafeIndex sample1s l0Index)
            (fromIntegral ((y1 `div` 8192) * 8192 + 1))
    pMax = Primitive.unsafeIndex sample1s (fromIntegral ((y1 `div` 8192) * 8192 + 1))
    l1Lo = Primitive.unsafeIndex l1l2s    (pMin `div` 2048)
    l1Hi = Primitive.unsafeIndex l1l2s    (pMax `div` 2048)
    l1l2 = search 
-}
