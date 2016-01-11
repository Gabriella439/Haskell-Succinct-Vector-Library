{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}

{-@ LIQUID "--real" @-}

-- module Succinct.Vector where

import Control.Monad (when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.))
import Data.Word (Word64)
import Data.Primitive.Types (Prim(..))
import Prelude hiding ((>>))

import qualified Control.Monad.ST              as ST
import qualified Data.Bits                     as Bits
import qualified Data.Vector.Primitive         as Primitive
import qualified Data.Vector.Primitive.Mutable as Mutable

{-@ measure vlen :: Primitive.Vector a -> Int @-}

{-@
assume Primitive.length
    :: Prim a => v : Primitive.Vector a -> { n : Int | 0 <= n && n = vlen v }
@-}

{-@
Primitive.unsafeIndex
    :: Prim a
    => v : Primitive.Vector a -> { n : Int | 0 <= n && n < vlen v } -> a
@-}

{-@ measure mlen :: Primitive.MVector (PrimState m) a -> Int @-}

-- TODO: Use unsafe writes once we can satisfy the Liquid Haskell type-checker
{-@
assume Mutable.unsafeWrite
    :: (PrimMonad m, Prim a)
    => v : Mutable.MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < mlen v }
    -> a
    -> m ()
@-}

{-@
assume Mutable.new
    :: (PrimMonad m, Prim a)
    => n : Int -> m ({ v : Mutable.MVector (PrimState m) a | mlen v == n })
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
l2_0 w64 = w64 .&. 0x000003FF00000000 >> 32

{- l2_1 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_1 :: Word64 -> Word64
l2_1 w64 = w64 .&. 0x000FFC0000000000 >> 42

{- l2_2 :: Word64 -> { v : Word64 | v < 1024 } -}
l2_2 :: Word64 -> Word64
l2_2 w64 = w64 .&. 0x3FF0000000000000 >> 52

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

{-@
data SuccinctBitVector = SuccinctBitVector
    { vector :: Primitive.Vector Word64
    , l0s    :: { l0s : Primitive.Vector Word64 | vlen l0s = (vlen vector / 67108864) + 1 }
    , l1l2s  :: { l1l2s : Primitive.Vector Word64 | vlen l1l2s = (vlen vector / 32) + 1 }
    }
@-}

data SuccinctBitVector = SuccinctBitVector
    { vector :: {-# UNPACK #-} !(Primitive.Vector Word64)
    , l0s    :: {-# UNPACK #-} !(Primitive.Vector Word64)
    , l1l2s  :: {-# UNPACK #-} !(Primitive.Vector Word64)
    } deriving (Show)

size :: SuccinctBitVector -> Int
size sbv = Primitive.length (vector sbv) * 64

prepare :: Primitive.Vector Word64 -> SuccinctBitVector
prepare vector = ST.runST (do
    l0sMutable   <- Mutable.new (quot (Primitive.length vector) 67108864 + 1)
    l1l2sMutable <- Mutable.new (quot (Primitive.length vector) 32       + 1)

    let count j =
            if j < Primitive.length vector
            then popCount (Primitive.unsafeIndex vector j)
            else 0

    -- TODO: Prove that `loop` terminates
    let {-@ Lazy loop @-}
        loop !i0 !previousCount !currentCount
            | i0 <= Primitive.length vector = do
                let (p0, q0) = quotRem i0 67108864
                previousCount' <-
                    if (q0 == 0)
                    then do
                        Mutable.write l0sMutable p0 currentCount
                        return currentCount
                    else return previousCount

                let {-@
                    assume l1_ :: { l1 : Word64 | 0 <= l1 && l1 < 4294967296 }
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
                Mutable.write l1l2sMutable p1 l1l2_

                let currentCount' = currentCount + l2_0_ + l2_1_ + l2_2_ + l2_3_
                loop i4 previousCount' currentCount'
            | otherwise = return ()
    loop 0 0 0

    {-@
    assume freezel0s
        :: vector : Primitive.Vector Word64
        -> ST s ({ l0s : Primitive.Vector Word64 | vlen l0s = (vlen vector / 67108864) + 1 })
    @-}
    let freezel0s _vector = Primitive.freeze l0sMutable
          where
            _ = _vector :: Primitive.Vector Word64
    l0s <- freezel0s vector

    {-@
    assume freezel1l2s
        :: vector : Primitive.Vector Word64
        -> ST s ({ l1l2s : Primitive.Vector Word64 | vlen l1l2s = (vlen vector / 32) + 1 })
    @-}
    let freezel1l2s _vector = Primitive.freeze l1l2sMutable
          where
            _ = _vector :: Primitive.Vector Word64
    l1l2s <- freezel1l2s vector

    return (SuccinctBitVector {..}) )

main :: IO ()
main = prepare (Primitive.enumFromN 0 10000000) `seq` return ()

{-@
unsafeRank
    :: sbv : SuccinctBitVector
    -> { bit : Int | 0 <= bit && bit <= vlen (vector sbv) * 64 }
    -> Word64
@-}
unsafeRank :: SuccinctBitVector -> Int -> Word64
unsafeRank sbv@(SuccinctBitVector {..}) bit = c0
  where
    -- TODO: Use `quot` when Liquid Haskell Prelude is fixed
    c0   = Primitive.unsafeIndex l0s   (div bit 4294967296)
    l1l2 = Primitive.unsafeIndex l1l2s (div bit 2048      )
