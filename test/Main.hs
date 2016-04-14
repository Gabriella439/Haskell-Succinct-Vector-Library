module Main where

import Data.Word (Word64)
import Succinct.Vector
import Test.DocTest (doctest)
import Test.QuickCheck hiding (vector)

import qualified Data.Vector.Primitive as Primitive

testL :: SuccinctBitVector -> Small Int -> Property
testL sbv (Small n) =
        0 <= n
    ==> n <  Primitive.length (vector sbv) * 64
    ==> n <= unsafeSelect sbv (unsafeRank sbv n)

testR :: SuccinctBitVector -> Small Word64 -> Property
testR sbv (Small w64) =
        0   <= w64
    ==> w64 <  numOnes sbv
    ==> w64 == unsafeRank sbv (unsafeSelect sbv w64)

main :: IO ()
main = do
    quickCheck testL
    quickCheck testR
    doctest ["src/Succinct/Vector.hs"]
