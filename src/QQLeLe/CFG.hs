
{-
 - qqlele/src/QQLeLe/CFG.hs
 - copyright (c) 2014 Frano Perleta
 -}

-- extensions {{{
{-# LANGUAGE
        FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving,
        MultiParamTypeClasses, OverlappingInstances, RankNTypes, UndecidableInstances
    #-}
-- }}}

-- exports {{{
module QQLeLe.CFG

    -- basic blocks:
    ( BBlock(..)
    , BB()

    -- graphs:
    , CFGT()
    , runCFGT
    , MonadCFG(..)

    -- graph operations:
    , rootBB
    , newBB
    , writeBB
    , readBB
    , predBB
    , succBB

    -- traversal:
    , reachableBBs
    , traverseBBs
    , traverseBBs_

    ) where
-- }}}

-- imports {{{
import           Control.Applicative
import           Control.Monad.State
import qualified Data.IntMap as IM
import           Data.IntMap (IntMap)
import qualified Data.IntSet as IS
import           Data.IntSet (IntSet)
-- }}}

-- basic blocks {{{

class BBlock bb where
    bblockSucc :: bb g -> [BB g]
    bblockRefs :: bb g -> [BB g]

-- }}}

-- graphs {{{

data CFG bb g = CFG
    { cfgNext :: {-# UNPACK #-} !Int
    , cfgBBlocks :: IntMap (bb g)
    , cfgPred :: IntMap IntSet
    , cfgSucc :: IntMap IntSet
    }

newtype BB g = BB { unBB :: Int }
  deriving (Eq, Ord)

cfgEmpty :: CFG bb g
cfgEmpty = CFG 0 IM.empty IM.empty IM.empty

cfgUpdate :: (BBlock bb) => BB g -> bb g -> CFG bb g -> CFG bb g
cfgUpdate (BB k) x (CFG n bbs pss sss) = CFG n bbs pss' sss
  where
    ss = IM.findWithDefault IS.empty k sss
    ss' = IS.fromList . map unBB $ bblockSucc x
    stale = IM.fromSet (const $ IS.singleton k) $ ss `IS.difference` ss'
    fresh = IM.fromSet (const $ IS.singleton k) $ ss' `IS.difference` ss
    pss' = IM.unionWith IS.union fresh $ IM.unionWith IS.difference pss stale

-- }}}

-- the monad transformer {{{

newtype CFGT bb g m a = CFGT { unCFGT :: StateT (CFG bb g) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)

runCFGT :: (Monad m) => (forall g. CFGT bb g m a) -> m a
runCFGT (CFGT body) = evalStateT body cfgEmpty

class (Monad m) => MonadCFG bb g m | m -> bb g where
    cfgState :: (CFG bb g -> (a, CFG bb g)) -> m a

instance (Monad m) => MonadCFG bb g (CFGT bb g m) where
    cfgState = CFGT . state

instance (MonadCFG bb g m, Monad (t m), MonadTrans t) => MonadCFG bb g (t m) where
    cfgState = lift . cfgState

-- }}}

-- operations {{{

rootBB :: (MonadCFG bb g m) => m (Maybe (BB g))
rootBB = cfgState $ \g -> let
    { res = case cfgNext g of
        0 -> Nothing
        _ -> Just $ BB 0
    } in (res, g)

newBB :: (MonadCFG bb g m, BBlock bb) => bb g -> m (BB g)
newBB x = cfgState $ \g -> let
    { k = cfgNext g
    ; r = BB k
    ; bbs = IM.insert k x $ cfgBBlocks g
    ; g' = g { cfgNext = succ k, cfgBBlocks = bbs }
    } in (r, cfgUpdate r x g')

writeBB :: (MonadCFG bb g m, BBlock bb) => BB g -> bb g -> m ()
writeBB r@(BB k) x = cfgState $ \g -> let
    { bbs = IM.insert k x $ cfgBBlocks g
    ; g' = g { cfgBBlocks = bbs }
    } in ((), cfgUpdate r x g')

readBB :: (MonadCFG bb g m) => BB g -> m (bb g)
readBB (BB k) = cfgState $ \g -> case IM.lookup k $ cfgBBlocks g of
    Just x -> (x, g)
    Nothing -> error "readBB: invalid basic block reference"

predBB :: (MonadCFG bb g m) => BB g -> m [BB g]
predBB (BB k) = cfgState $ \g -> let
    { ps = IM.findWithDefault IS.empty k $ cfgPred g
    } in (map BB $ IS.toList ps, g)

succBB :: (MonadCFG bb g m) => BB g -> m [BB g]
succBB (BB k) = cfgState $ \g -> let
    { ss = IM.findWithDefault IS.empty k $ cfgSucc g
    } in (map BB $ IS.toList ss, g)

-- }}}

-- traversal {{{

reachableBBs :: (MonadCFG bb g m) => m [BB g]
reachableBBs = do
    mroot <- rootBB
    case mroot of
        Just root -> traverseBBs root $ \bb -> do
            ss <- succBB bb
            return (bb, ss)
        Nothing -> return []

traverseBBs :: (MonadCFG bb g m) => BB g -> (BB g -> m (a, [BB g])) -> m [a]
traverseBBs from action = go IS.empty [from]
  where
    go _ [] = return []
    go seen (bb@(BB k) : rest)
        | k `IS.member` seen = go seen rest
        | otherwise = do
            (x, ss) <- action bb
            (x :) `liftM` go (IS.insert k seen) (ss ++ rest)

traverseBBs_ :: (MonadCFG bb g m) => BB g -> (BB g -> m [BB g]) -> m ()
traverseBBs_ from action = go IS.empty [from]
  where
    go _ [] = return ()
    go seen (bb@(BB k) : rest)
        | k `IS.member` seen = go seen rest
        | otherwise = do
            ss <- action bb
            go (IS.insert k seen) (ss ++ rest)

-- }}}

-- vim:fdm=marker:
