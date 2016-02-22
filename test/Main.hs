module Main where

import Data.Word (Word64)
import qualified Data.Vector as DV
import Succinct.Vector
import Test.DocTest (doctest)
import Test.QuickCheck

testL :: SuccinctBitVector a => a -> Small Word64 -> Property
testL sbv (Small w64) =
        (c0 < fst (partialRank sbv n))
    ==> (c0 == c1 + c2)
  where
    -- The (-1) correction is because several indices only support `rank` for
    -- `Position`s less than the index `size`
    n = max 0 (size sbv - 1)

    c0 = Count w64

    (p1, c1) = partialSelect sbv c0
    (c2, _ ) = partialRank   sbv p1

testR :: SuccinctBitVector a => a -> Small Int -> Property
testR sbv (Small i) =
        (0 <= p0 && p0 <= size sbv)
    ==> (c1 < fst (partialRank sbv n))
    ==> (p0 <= p1 + p2)
  where
    n = max 0 (size sbv - 1)

    p0 = Position i

    (c1, p1) = partialRank   sbv p0
    (p2, _ ) = partialSelect sbv c1

word64L :: Word64 -> Small Word64 -> Property
word64L = testL

word64R :: Word64 -> Small Int -> Property
word64R = testR

basicBlockL :: BasicBlock -> Small Word64 -> Property
basicBlockL = testL

basicBlockR :: BasicBlock -> Small Int -> Property
basicBlockR = testR

intermediateBlockL :: IntermediateBlock -> Small Word64 -> Property
intermediateBlockL = testL

intermediateBlockR :: IntermediateBlock -> Small Int -> Property
intermediateBlockR = testR

superBlockL :: IntermediateBlock -> Small Word64 -> Property
superBlockL = testL

superBlockR :: IntermediateBlock -> Small Int -> Property
superBlockR = testR

bitVectorL :: BitVector -> Small Word64 -> Property
bitVectorL = testL

bitVectorR :: BitVector -> Small Int -> Property
bitVectorR = testR

data VectorRank = VectorRank [Word64] Position deriving (Eq, Show)

data LenAsPos = LenAsPos VectorRank deriving (Eq, Show)

instance Arbitrary LenAsPos where
  arbitrary = do
    h <- arbitrary :: Gen Word64
    v <- arbitrary :: Gen [Word64]
    let n = (length v + 1) * 64 :: Int
    return (LenAsPos (VectorRank (h:v) (Position n)))

workingLenPos :: Property
workingLenPos = property $
    \(LenAsPos (VectorRank as i)) ->
      let nv = prepare (DV.fromList as :: DV.Vector Word64) in
      rank nv i == rank nv i

main :: IO ()
main = do
    quickCheck word64L
    quickCheck word64R
    quickCheck basicBlockL
    quickCheck basicBlockR
    quickCheck intermediateBlockL
    quickCheck intermediateBlockR
    quickCheck superBlockL
    quickCheck superBlockR
    quickCheck bitVectorL
    quickCheck bitVectorR
    quickCheck workingLenPos
    doctest ["src/Succinct/Vector.hs"]
