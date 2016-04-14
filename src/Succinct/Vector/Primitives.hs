module Succinct.Vector.Primitives where

import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST)
import Data.Primitive.Types (Prim)

import qualified Data.Vector.Primitive
import qualified Data.Vector.Primitive.Mutable

{-@ measure plen :: Data.Vector.Primitive.Vector a -> Int @-}

{-@
assume Data.Vector.Primitive.length
    :: Prim a
    => v : Data.Vector.Primitive.Vector a -> { n : Int | 0 <= n && n == plen v }
@-}

{-@
Data.Vector.Primitive.unsafeIndex
    :: Prim a
    => v : Data.Vector.Primitive.Vector a
    -> { n : Int | 0 <= n && n < plen v }
    -> a
@-}

{-@
assume Data.Vector.Primitive.unsafeSlice
    :: Prim a
    => n : { n : Int | 0 <= n }
    -> l : { l : Int | 0 <= l }
    -> i : { i : Data.Vector.Primitive.Vector a | n + l <= plen i }
    -> { o : Data.Vector.Primitive.Vector a | plen o = l }
@-}

{-@ measure pmlen :: Data.Vector.Primitive.Mutable.MVector s a -> Int @-}

{-@
assume Data.Vector.Primitive.Mutable.length
    :: Prim a
    => v : Data.Vector.Primitive.Mutable.MVector s a
    -> { n : Int | 0 <= n && n == pmlen v }
@-}

{-@
assume Data.Vector.Primitive.Mutable.unsafeWrite
    :: (PrimMonad m, Prim a)
    => v : Data.Vector.Primitive.Mutable.MVector (PrimState m) a
    -> { n : Int | 0 <= n && n < pmlen v }
    -> a
    -> m ()
@-}

{-@
assume primitiveNewST
    :: Prim a
    => n : Int
    -> ST s ({ v : Data.Vector.Primitive.Mutable.MVector s a | pmlen v == n })
@-}
primitiveNewST
    :: Prim a => Int -> ST s (Data.Vector.Primitive.Mutable.MVector s a)
primitiveNewST = Data.Vector.Primitive.Mutable.new
{-# INLINE primitiveNewST #-}

{-@
qualif New(v : Data.Vector.Primitive.Mutable.MVector s a, n : Int) : pmlen v == n
@-}

{-@
assume primitiveFreezeST
    :: Prim a
    => mv : Data.Vector.Primitive.Mutable.MVector s a
    -> ST s ({ v : Data.Vector.Primitive.Vector a | plen v == pmlen mv })
@-}
primitiveFreezeST
    :: Prim a
    => Data.Vector.Primitive.Mutable.MVector s a
    -> ST s (Data.Vector.Primitive.Vector a)
primitiveFreezeST = Data.Vector.Primitive.freeze
{-# INLINE primitiveFreezeST #-}

{-| Finds the last element in the vector that is less than or equal to `x`
    when transformed using function `f`

    TODO: This assumes that there is at least one element in the vector less
    than or equal to `x`
-}
{-@
search
    :: (Prim e, Ord a)
    => x  : a
    -> f  : (e -> a)
    -> v  : Data.Vector.Primitive.Vector e
    -> lo : { lo : Int | 0  <= lo && lo <  plen v }
    -> hi : { hi : Int | lo <  hi && hi <= plen v }
    ->      { r  : Int | lo <= r  && r  <  hi     }
    /  [hi - lo]
@-}
search
    :: (Ord a, Prim e)
    => a -> (e -> a) -> Data.Vector.Primitive.Vector e -> Int -> Int -> Int
search x f v lo hi = do
    if lo + 1 == hi
    then lo
    else do
        let mid = lo + (hi - lo) `div` 2
        let x' = f (Data.Vector.Primitive.unsafeIndex v mid)
        if x < x'
        then search x f v lo  mid
        else search x f v mid hi
