{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Imp.Common (
  module X,
  io,

  -- * Expectations

  -- ** Lifted expectations
  assertBool,
  assertFailure,
  assertColorFailure,
  expectationFailure,
  shouldBe,
  shouldSatisfy,
  shouldSatisfyExpr,
  shouldStartWith,
  shouldEndWith,
  shouldContain,
  shouldMatchList,
  shouldReturn,
  shouldNotBe,
  shouldNotSatisfy,
  shouldNotContain,
  shouldNotReturn,
  shouldThrow,

  -- ** Non-standard expectations
  shouldBeExpr,
  shouldBeRight,
  shouldBeLeft,
  shouldBeRightExpr,
  shouldBeLeftExpr,
  shouldContainExpr,
  expectRight,
  expectRightDeep_,
  expectRightDeep,
  expectRightExpr,
  expectRightDeepExpr,
  expectLeft,
  expectLeftDeep_,
  expectLeftExpr,
  expectLeftDeep,
  expectLeftDeepExpr,
  expectJust,
  expectNothingExpr,

  -- * MonadGen
  module QuickCheckT,
  arbitrary,
  -- TODO: add here any other lifted functions from quickcheck

  -- * Random interface
  HasStatefulGen (..),
  R.StatefulGen,
  uniformM,
  uniformRM,
  uniformListM,
  uniformListRM,
  uniformByteStringM,
  uniformShortByteStringM,

  -- * Re-exports from ImpSpec
  withImpInit,
  modifyImpInit,

  describe,
  it,
  lastTestState,
  globalTestState,
  globalStates,
  dumpEvent,
  annotations,
  dumpProtocolVersion,
  DumpEvent (..),
  InitialConfig (..),
  initialConfig
)
where

import Cardano.Slotting.Slot (SlotNo (..), EpochNo (..), EpochSize(..))
import Control.Monad.IO.Class
import Data.List (intercalate, isInfixOf)
import qualified System.Random.Stateful as R
import Cardano.Ledger.Binary.Encoding (EncCBOR(..), Encoding, serialize, encodeListLen)
import Test.Cardano.Ledger.Binary.TreeDiff (expectExprEqualWithMessage)
import Cardano.Ledger.Binary.Version (Version)
import Test.Cardano.Ledger.Common as X hiding (
  arbitrary,
  assertBool,
  assertColorFailure,
  assertFailure,
  choose,
  describe,
  elements,
  expectLeft,
  expectLeftDeep,
  expectLeftDeepExpr,
  expectLeftDeep_,
  expectLeftExpr,
  expectRight,
  expectRightDeep,
  expectRightDeepExpr,
  expectRightDeep_,
  expectRightExpr,
  expectationFailure,
  frequency,
  growingElements,
  it,
  listOf,
  listOf1,
  oneof,
  resize,
  shouldBe,
  shouldBeExpr,
  shouldBeLeft,
  shouldBeLeftExpr,
  shouldBeRight,
  shouldBeRightExpr,
  shouldContain,
  shouldEndWith,
  shouldMatchList,
  shouldNotBe,
  shouldNotContain,
  shouldNotReturn,
  shouldNotSatisfy,
  shouldReturn,
  shouldSatisfy,
  shouldStartWith,
  shouldThrow,
  sized,
  suchThat,
  suchThatMaybe,
  variant,
  vectorOf,
 )
import qualified Test.Cardano.Ledger.Common as Common
import Test.ImpSpec (modifyImpInit, withImpInit)
import Test.ImpSpec.Expectations.Lifted
import Test.ImpSpec.Random (
  HasStatefulGen (..),
  arbitrary,
  uniformByteStringM,
  uniformListM,
  uniformListRM,
  uniformM,
  uniformRM,
  uniformShortByteStringM,
 )
import Test.QuickCheck.GenT as QuickCheckT
import UnliftIO (MonadUnliftIO (..))
import UnliftIO.Exception (evaluateDeep)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, modifyIORef, readIORef)
import Test.Hspec.Core.Spec as X (getSpecDescriptionPath)

import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified System.Directory as Directory
import Cardano.Ledger.Binary.Coders (Encode (..), encode, (!>))

import Data.Word (Word64)
import Cardano.Slotting.Time (SystemStart(..))
import Cardano.Ledger.BaseTypes (ActiveSlotCoeff, mkActiveSlotCoeff, Globals(..), Network)
import Data.Time.Clock (UTCTime(..))

instance MonadUnliftIO m => MonadUnliftIO (GenT m) where
  withRunInIO inner = GenT $ \qc sz ->
    withRunInIO $ \run -> inner $ \(GenT f) -> run (f qc sz)

infix 1 `shouldBeExpr`
        , `shouldBeRightExpr`
        , `shouldBeLeftExpr`

shouldBeExpr :: (HasCallStack, ToExpr a, Eq a, MonadIO m) => a -> a -> m ()
shouldBeExpr expected actual = liftIO $ expectExprEqualWithMessage "" expected actual

shouldSatisfyExpr :: (HasCallStack, MonadIO m, ToExpr a) => a -> (a -> Bool) -> m ()
shouldSatisfyExpr x f
  | f x = pure ()
  | otherwise = assertFailure $ "predicate failed on:\n" <> showExpr x

shouldContainExpr :: (HasCallStack, ToExpr a, Eq a, MonadIO m) => [a] -> [a] -> m ()
shouldContainExpr x y
  | y `isInfixOf` x = pure ()
  | otherwise =
      assertFailure $
        "First list does not contain the second list:\n"
          <> showExpr x
          <> "\ndoes not contain\n"
          <> showExpr y

-- | Same as `expectRight`, but use `ToExpr` instead of `Show`
expectRightExpr :: (HasCallStack, ToExpr a, MonadIO m) => Either a b -> m b
expectRightExpr (Right r) = pure $! r
expectRightExpr (Left l) = assertFailure $ "Expected Right, got Left:\n" <> showExpr l

-- | Same as `expectRightDeep`,  but use `ToExpr` instead of `Show`
expectRightDeepExpr :: (HasCallStack, ToExpr a, NFData b, MonadIO m) => Either a b -> m b
expectRightDeepExpr = expectRightExpr >=> evaluateDeep

-- | Same as `shouldBeExpr`, except it checks that the value is `Right`
shouldBeRightExpr :: (HasCallStack, ToExpr a, Eq b, ToExpr b, MonadIO m) => Either a b -> b -> m ()
shouldBeRightExpr e x = expectRightExpr e >>= (`shouldBeExpr` x)

-- | Same as `expectLeft`, but use `ToExpr` instead of `Show`
expectLeftExpr :: (HasCallStack, ToExpr b, MonadIO m) => Either a b -> m a
expectLeftExpr (Left l) = pure $! l
expectLeftExpr (Right r) = assertFailure $ "Expected Left, got Right:\n" <> showExpr r

-- | Same as `expectLeftDeep`,  but use `ToExpr` instead of `Show`
expectLeftDeepExpr :: (HasCallStack, ToExpr b, NFData a, MonadIO m) => Either a b -> m a
expectLeftDeepExpr = expectLeftExpr >=> evaluateDeep

-- | Same as `shouldBeExpr`, except it checks that the value is `Left`
shouldBeLeftExpr :: (HasCallStack, ToExpr a, ToExpr b, Eq a, MonadIO m) => Either a b -> a -> m ()
shouldBeLeftExpr e x = expectLeftExpr e >>= (`shouldBeExpr` x)

expectNothingExpr :: (HasCallStack, MonadIO m, ToExpr a) => Maybe a -> m ()
expectNothingExpr (Just x) =
  assertFailure $
    "Expected Nothing, got Just:\n" <> showExpr x
expectNothingExpr Nothing = pure ()

describe :: String -> SpecWith a -> SpecWith a
describe s spec = Common.describe s spec

it :: (Example a, MonadIO m, m () ~ a) => String -> a -> SpecWith (Arg a)
it s spec = do
  p <- getSpecDescriptionPath
  Common.it s $ do
    let ts = p ++ [s]
    liftIO $ modifyIORef globalTestState (const ts)
    spec
    txes <- liftIO $ deduplicate <$> readIORef dumpEvent
    states <- liftIO $ readIORef globalStates
    protocolVersion <- liftIO $ readIORef dumpProtocolVersion
    ic <- liftIO $ readIORef initialConfig
    let doDump = do
          let sanitize = map $ \c -> if c == '/' then '-' else c
          let dirPath = intercalate "/" $ map sanitize (init ts)
          let file = sanitize (last ts)
          Directory.createDirectoryIfMissing True ("dump/" ++ dirPath)
          BS.writeFile
            ("dump/" ++ dirPath ++ "/" ++ file)
            (BS.toStrict $ (serialize protocolVersion
              ( ic
              , if null states then encCBOR ([] :: [()]) else head states
              , if null states then encCBOR ([] :: [()]) else last states
              , txes
              , T.pack (dirPath ++ "/" ++ file)
              )))
    when
      (not (null states))
      (liftIO doDump)
    liftIO $ modifyIORef globalTestState (const [])
    liftIO $ modifyIORef globalStates (const [])
    liftIO $ modifyIORef dumpEvent (const [])
    liftIO $ modifyIORef annotations (const [])

lastTestState :: IORef (Maybe [String])
lastTestState = unsafePerformIO $ newIORef Nothing

globalTestState :: IORef [String]
globalTestState = unsafePerformIO $ newIORef []

globalStates :: IORef [Encoding]
globalStates = unsafePerformIO $ newIORef []

dumpEvent :: IORef [DumpEvent]
dumpEvent = unsafePerformIO $ newIORef []

annotations :: IORef [String]
annotations = unsafePerformIO $ newIORef []

dumpProtocolVersion :: IORef Version
dumpProtocolVersion = unsafePerformIO $ newIORef minBound

initialConfig :: IORef InitialConfig
initialConfig = unsafePerformIO $ newIORef $
  InitialConfig
    { initialSlot = 0
    , initialEpoch = EpochNo 0
    , epochLength = EpochSize 0
    , icGlobals = Globals
        { epochInfo = undefined
        , slotsPerKESPeriod = 0
        , stabilityWindow = 0
        , randomnessStabilisationWindow = 0
        , securityParameter = 0
        , maxKESEvo = 0
        , quorum = 0
        , maxLovelaceSupply = 0
        , activeSlotCoeff = mkActiveSlotCoeff minBound
        , networkId = minBound
        , systemStart = SystemStart (UTCTime (toEnum 0) 0)
        }
    }

data DumpEvent
  = EventTransaction Encoding Bool SlotNo
  | EventPassTick Int
  | EventPassEpoch Int

-- Merge sequential passTick and passEpoch events
deduplicate :: [DumpEvent] -> [DumpEvent]
deduplicate ((EventPassTick x):(EventPassTick y):zs) = deduplicate (EventPassTick (x + y) : zs)
deduplicate ((EventPassEpoch x):(EventPassEpoch y):zs) = deduplicate (EventPassEpoch (x + y) : zs)
deduplicate (x:xs) = x : deduplicate xs
deduplicate [] = []

instance EncCBOR DumpEvent where
  encCBOR (EventTransaction e b s) =
    encode $
      Sum EventTransaction 0
        !> To e
        !> To b
        !> To s
  encCBOR (EventPassTick n) =
    encode $
      Sum EventPassTick 1
        !> To n
  encCBOR (EventPassEpoch n) =
    encode $
      Sum EventPassEpoch 2
        !> To n

-- Modified represntation of globals that is CBOR-serializable
data InitialConfig
  = InitialConfig
    { initialSlot :: SlotNo
    , initialEpoch :: EpochNo
    , epochLength :: EpochSize
    , icGlobals :: Globals
    }

instance EncCBOR InitialConfig where
  encCBOR (InitialConfig {..}) =
    encodeListLen 13 <>
    encCBOR initialSlot <>
    encCBOR initialEpoch <>
    encCBOR epochLength <>
    encCBOR (slotsPerKESPeriod icGlobals) <>
    encCBOR (stabilityWindow icGlobals) <>
    encCBOR (randomnessStabilisationWindow icGlobals) <>
    encCBOR (securityParameter icGlobals) <>
    encCBOR (maxKESEvo icGlobals) <>
    encCBOR (quorum icGlobals) <>
    encCBOR (maxLovelaceSupply icGlobals) <>
    encCBOR (activeSlotCoeff icGlobals) <>
    encCBOR (networkId icGlobals) <>
    encCBOR (systemStart icGlobals)
