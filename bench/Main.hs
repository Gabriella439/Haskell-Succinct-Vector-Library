module Main where

import Criterion.Main
import Data.Word (Word64)
import Succinct.Vector

import qualified Data.Vector.Primitive as Primitive

v :: Primitive.Vector Word64
v = Primitive.fromList (take 1000000 (cycle [maxBound, 0]))

setupEnv :: IO SuccinctBitVector
setupEnv = return (prepare v)

main :: IO ()
main = defaultMain
    [ env setupEnv (\idx -> bgroup "Rank"
        [ bench "Once" (whnf (unsafeRank idx) 10)
        , bench "Once" (whnf (unsafeSelect idx) 10)
        , bench "Many" (nf   (map (unsafeRank idx)) [0,1000..64000000])
        ] )
    ]
