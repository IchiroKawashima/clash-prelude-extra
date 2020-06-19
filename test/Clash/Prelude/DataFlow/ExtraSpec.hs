module Clash.Prelude.DataFlow.ExtraSpec
    ( spec
    )
where

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Clash.Prelude
import qualified Data.List                     as L
import           Data.Tuple.Extra

import           Clash.Prelude.DataFlow.Extra

df2f :: forall dom i o iEn oEn
      . KnownDomain dom
     => NFDataX i
     => NFDataX iEn
     => NFDataX oEn
     => NFDataX o => DataFlow dom iEn oEn i o -> (i, iEn, oEn) -> (o, oEn, iEn)
df2f f = L.head . simulateB (uncurry3 $ df f) . (: [])

spec :: Spec
spec = do

    let repeater :: (Int, Int) -> (Int, Maybe (Int, Int))
        repeater (n, c) = let c' = c - 1 in (n, if c' <= 0 then Nothing else Just (n, c'))

        counter :: Maybe (Int, Int) -> Int -> (Int, Int)
        counter acc n' = case acc of
            Nothing     -> (n', 1)
            Just (_, c) -> (n', c + 1)

    describe "decompressLogic" $ do

        let target = ((.) . (.))
                (\(t, ((l, d), v, r)) -> (t, ((maybeIsX l, maybeIsX d), v, r)))
                (decompressLogic repeater)

        it "does nothing when not ivld or not ordy when it has not data (i.e. state = Nothing)" $ do
            target decompressInit (undefined, False, False)
                `shouldBe` (decompressInit, ((Nothing, Nothing), False, False))
            target decompressInit (undefined, False, True)
                `shouldBe` (decompressInit, ((Nothing, Nothing), False, True))
            target decompressInit ((3, 1), True, False)
                `shouldBe` (decompressInit, ((Just True, Just 3), True, False))

        it "asserts last and becomes the initial state when it does not have any more data" $ do
            target decompressInit ((5, 1), True, True)
                `shouldBe` (decompressInit, ((Just True, Just 5), True, True))
            target (Just (7, 1)) (undefined, undefined, True)
                `shouldBe` (decompressInit, ((Just True, Just 7), True, False))

        it "does not assert last when it has some more data" $ do
            target decompressInit ((9, 2), True, True)
                `shouldBe` (Just (9, 1), ((Just False, Just 9), True, True))
            target (Just (11, 2)) (undefined, undefined, True)
                `shouldBe` (Just (11, 1), ((Just False, Just 11), True, False))

        prop "keeps data when it has data and not ordy" $ \state@(n, c) ->
            (c > 0)
                ==> target (Just state) (undefined, undefined, False)
                ==  (Just state, ((Just (c == 1), Just n), True, False))

    describe "compressLogic" $ do

        let target =
                ((.) . (.)) (\(b, (d, v, r)) -> (b, (maybeIsX d, v, r))) (compressLogic counter)

        it "does nothing when not ivld or not ordy when it has data (i.e. iData = Left ~)" $ do
            target compressInit (undefined, False, False)
                `shouldBe` (compressInit, (Nothing, False, True))
            target compressInit (undefined, False, True)
                `shouldBe` (compressInit, (Nothing, False, True))
            target compressInit ((True, 3), True, False)
                `shouldBe` (compressInit, (Just (3, 1), True, False))

        it "becomes the initial state when it gets the last data" $ do
            target compressInit ((True, 3), True, True)
                `shouldBe` (compressInit, (Just (3, 1), True, True))
            target (Just (5, 1)) ((True, 5), True, True)
                `shouldBe` (compressInit, (Just (5, 2), True, True))

        it "does not output data when it does not get the last data" $ do
            target Nothing ((False, 7), True, undefined)
                `shouldBe` (Just (7, 1), (Just (7, 1), False, True))
            target (Just (9, 1)) ((False, 7), True, undefined)
                `shouldBe` (Just (7, 2), (Just (7, 2), False, True))

        prop "keeps data when it has data and not ordy" $ \state@(n, c) ->
            (c > 0)
                ==> target (Just state) ((True, n), True, False)
                ==  (Just state, (Just (n, c + 1), True, False))

    describe "decompressDF & compressDF" $ do

        let target :: (Int, Int) -> (Int, Int)
            target =
                fst
                    . L.head
                    . simulateDF @System
                          (       hideClockResetEnable decompressDF repeater
                          `seqDF` hideClockResetEnable compressDF   counter
                          )
                    . L.replicate 1

        it "reconstruct given data" $ do

            target (3, 1) `shouldBe` (3, 1)
            target (5, 2) `shouldBe` (5, 2)
            target (7, 5) `shouldBe` (7, 5)

    describe "selectStep" $ do

        let target :: forall i o iEn
                    . NFDataX i
                   => NFDataX o
                   => NFDataX iEn => SelectStep iEn i o => (i, iEn, Bool) -> (o, Bool, iEn)
            target = df2f @System selectStep


        it "behaves as idDF when there is no branch" $ do

            let target' = (\(d, v, r) -> (maybeIsX d, v, r)) . target @Int @Int

            target' (undefined, False, False) `shouldBe` (Nothing, False, False)
            target' (undefined, False, True) `shouldBe` (Nothing, False, True)
            target' (3, True, False) `shouldBe` (Just 3, True, False)
            target' (5, True, True) `shouldBe` (Just 5, True, True)


        it "collects given data with prioritising Left side when there is a branch" $ do

            let target' =
                    (\(d, v, r) -> (maybeHasX d, v, r)) . target @(Int, Int) @(Either Int Int)

            target' ((undefined, undefined), (False, False), False)
                `shouldBe` (Nothing, False, (False, False))
            target' ((undefined, 3), (False, True), False)
                `shouldBe` (Just (Right 3), True, (False, False))
            target' ((5, undefined), (True, False), False)
                `shouldBe` (Just (Left 5), True, (False, False))
            target' ((7, 11), (True, True), False) `shouldBe` (Just (Left 7), True, (False, False))
            target' ((undefined, undefined), (False, False), True)
                `shouldBe` (Nothing, False, (True, False))
            target' ((undefined, 13), (False, True), True)
                `shouldBe` (Just (Right 13), True, (False, True))
            target' ((17, undefined), (True, False), True)
                `shouldBe` (Just (Left 17), True, (True, False))
            target' ((19, 23), (True, True), True) `shouldBe` (Just (Left 19), True, (True, False))

    describe "stepSelect" $ do

        let target :: forall i o oEn
                    . NFDataX i
                   => NFDataX o
                   => NFDataX oEn => SelectStep oEn o i => (i, Bool, oEn) -> (o, oEn, Bool)
            target = df2f @System stepSelect

        it "behaves as idDF when there is no branch" $ do

            let target' = (\(d, v, r) -> (maybeIsX d, v, r)) . target @Int @Int

            target' (undefined, False, False) `shouldBe` (Nothing, False, False)
            target' (undefined, False, True) `shouldBe` (Nothing, False, True)
            target' (3, True, False) `shouldBe` (Just 3, True, False)
            target' (5, True, True) `shouldBe` (Just 5, True, True)

        it "distributes given data" $ do
            let target' =
                    (\((dl, dr), v, r) -> ((maybeIsX dl, maybeIsX dr), v, r))
                        . target @(Either Int Int) @(Int, Int)

            target' (undefined, False, (False, False))
                `shouldBe` ((Nothing, Nothing), (False, False), False)
            target' (undefined, False, (False, True))
                `shouldBe` ((Nothing, Nothing), (False, False), False)
            target' (undefined, False, (True, False))
                `shouldBe` ((Nothing, Nothing), (False, False), True)
            target' (undefined, False, (True, True))
                `shouldBe` ((Nothing, Nothing), (False, False), True)
            target' (Left 3, True, (False, False))
                `shouldBe` ((Just 3, Nothing), (True, False), False)
            target' (Right 5, True, (False, False))
                `shouldBe` ((Nothing, Just 5), (False, True), False)
            target' (Left 7, True, (False, True))
                `shouldBe` ((Just 7, Nothing), (True, False), False)
            target' (Right 11, True, (False, True))
                `shouldBe` ((Nothing, Just 11), (False, True), True)
            target' (Left 13, True, (True, False))
                `shouldBe` ((Just 13, Nothing), (True, False), True)
            target' (Right 17, True, (True, False))
                `shouldBe` ((Nothing, Just 17), (False, True), False)
            target' (Left 19, True, (True, True))
                `shouldBe` ((Just 19, Nothing), (True, False), True)
            target' (Right 23, True, (True, True))
                `shouldBe` ((Nothing, Just 23), (False, True), True)

    describe "sourceDF" $ do

        let target :: Int -> (Maybe Int, Int)
            target d =
                first maybeIsX
                    $ fst3
                    $ L.head
                    $ L.dropWhile (not . snd . snd3)
                    $ simulateB @System (uncurry3 $ df sourceDF)
                    $ L.repeat (d, True, (True, True))

        it "source does not emit any data" $ target 3 `shouldBe` (Nothing, 3)

    describe "queueDF" $ do

        let target :: forall mode
                    . SQueueMode mode
                   -> [(Int, Bool, Bool)]
                   -> [(Maybe Int, Bool, Bool)]
            target mode is =
                L.take (L.length is)
                    . L.map (\(d, v, r) -> (maybeIsX d, v, r))
                    . simulateB @System (uncurry3 $ df $ hideClockResetEnable queueDF mode)
                    $ is

        it "behaves as idDF in SNone mode" $ do

            --test patterns
            --valid,ready
            --00
            --01
            --10
            --11

            let i =
                    [ (undefined, False, False)
                    , (undefined, False, True)
                    , (2        , True , False)
                    , (3        , True , True)
                    ]

                o =
                    [ (Nothing, False, False)
                    , (Nothing, False, True)
                    , (Just 2 , True , False)
                    , (Just 3 , True , True)
                    ]

            target SNone i `shouldBe` o

        it "passes data intermittently in SMono mode" $ do

            --test patterns
            --state,valid,ready
            --000
            --001
            --010
            --100
            --101
            --011
            --110
            --111
            --000

            let i =
                    [ (undefined, False, False)
                    , (undefined, False, True)
                    , (2        , True , False)
                    , (undefined, False, False)
                    , (undefined, False, True)
                    , (3        , True , True)
                    , (5        , True , False)
                    , (7        , True , True)
                    , (undefined, False, False)
                    ]

                o =
                    [ (Nothing, False, True)
                    , (Nothing, False, True)
                    , (Nothing, False, True)
                    , (Just 2 , True , False)
                    , (Just 2 , True , False)
                    , (Just 2 , False, True)
                    , (Just 3 , True , False)
                    , (Just 3 , True , False)
                    , (Just 3 , False, True)
                    ]

            target SMono i `shouldBe` o

        it "passes data continuously in SMulti mode" $ do

            --test patterns
            --state,valid,ready, ,data
            --000 xx
            --001 xx
            --010 xx
            --100 2x
            --110 2x
            --200 23
            --210 23
            --201 23
            --101 3x
            --011 xx
            --111 7x
            --110 9x
            --211 91
            --101 1x
            --000 xx

            let i =
                    [ (undefined, False, False)
                    , (undefined, False, True)
                    , (2        , True , False)
                    , (undefined, False, False)
                    , (3        , True , False)
                    , (undefined, False, False)
                    , (5        , True , False)
                    , (undefined, False, True)
                    , (undefined, False, True)
                    , (7        , True , True)
                    , (9        , True , True)
                    , (11       , True , False)
                    , (13       , True , True)
                    , (undefined, False, True)
                    , (undefined, False, False)
                    ]

                o =
                    [ (Nothing, False, True)
                    , (Nothing, False, True)
                    , (Nothing, False, True)
                    , (Just 2 , True , True)
                    , (Just 2 , True , True)
                    , (Just 2 , True , False)
                    , (Just 2 , True , False)
                    , (Just 2 , True , False)
                    , (Just 3 , True , True)
                    , (Just 3 , False, True)
                    , (Just 7 , True , True)
                    , (Just 9 , True , True)
                    , (Just 9 , True , False)
                    , (Just 11, True , True)
                    , (Just 11, False, True)
                    ]

            target SMulti i `shouldBe` o
