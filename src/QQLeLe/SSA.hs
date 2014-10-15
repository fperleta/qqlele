
{-
 - qqlele/src/QQLeLe/SSA.hs
 - copyright (c) 2014 Frano Perleta
 -}

-- extensions {{{
{-# LANGUAGE
        FlexibleContexts, FlexibleInstances, FunctionalDependencies,
        GeneralizedNewtypeDeriving, KindSignatures, MultiParamTypeClasses,
        OverlappingInstances, RankNTypes, UndecidableInstances
    #-}
-- }}}

-- exports {{{
module QQLeLe.SSA

    -- variables:
    ( Var()
    , Vars()
    , FreeVars(..)
    , BoundVars(..)

    -- values:
    , Val(..)
    , UnOp(..)
    , BinOp(..)

    -- types:
    , VarType(..)

    -- basic blocks:
    , SSA(..)
    , Line(..)
    , Tail(..)
    , Target(..)
    , Condition(..)

    -- the monad transformer:
    , SSAT()
    , runSSAT
    , MonadSSA(..)

    -- variable attributes:
    , VarAttrT()
    , runVarAttrT
    , setVarAttr
    , getVarAttr

    ) where
-- }}}

-- imports {{{
import           Control.Applicative
import           Control.Monad.State.Strict
import qualified Data.IntMap as IM
import           Data.IntMap (IntMap)
import qualified Data.IntSet as IS
import           Data.IntSet (IntSet)
import           Data.Monoid
import           Data.Word

import           QQLeLe.CFG
import           QQLeLe.X86
-- }}}

-- variables {{{

newtype Var g = Var { unVar :: Int }
  deriving (Eq, Ord)

newtype Vars g = Vars { unVars :: IntSet }
  deriving (Eq, Ord)

instance Monoid (Vars g) where
    mempty = Vars IS.empty
    Vars x `mappend` Vars y = Vars $ x `IS.union` y
    mconcat = Vars . IS.unions . map unVars

singleVar :: Var g -> Vars g
singleVar (Var k) = Vars $ IS.singleton k

memberVar :: Var g -> Vars g -> Bool
memberVar (Var k) (Vars ks) = IS.member k ks

toVarList :: Vars g -> [Var g]
toVarList (Vars ks) = map Var $ IS.toList ks

fromVarList :: [Var g] -> Vars g
fromVarList xs = Vars . IS.fromList $ map unVar xs

withoutVars :: Vars g -> Vars g -> Vars g
Vars x `withoutVars` Vars y = Vars $ IS.difference x y

-- free variables {{{

class FreeVars g a | a -> g where
    freeVars :: a -> Vars g

instance FreeVars g (Var g) where
    freeVars = singleVar
    {-# INLINE freeVars #-}

instance FreeVars g (Vars g) where
    freeVars = id
    {-# INLINE freeVars #-}

instance FreeVars g [Var g] where
    freeVars = fromVarList
    {-# INLINE freeVars #-}

instance (FreeVars g a) => FreeVars g [a] where
    freeVars = mconcat . map freeVars
    {-# INLINE freeVars #-}

-- }}}

-- bound variables {{{

class BoundVars g a | a -> g where
    boundVars :: a -> Vars g

instance (BoundVars g a) => BoundVars g [a] where
    boundVars = mconcat . map boundVars
    {-# INLINE boundVars #-}

-- }}}

-- }}}

-- values {{{

data Val g
    = ValConst VarType Word64
    | ValUnOp UnOp (Var g)
    | ValBinOp BinOp (Var g) (Var g)

data UnOp
    = NotOp
    | NegOp

data BinOp
    = AndOp
    | OrOp
    | XorOp
    | AddOp
    | SubOp

instance FreeVars g (Val g) where
    freeVars val = case val of
        ValConst _ _ -> mempty
        ValUnOp _ x -> freeVars x
        ValBinOp _ x y -> freeVars [x, y]

-- }}}

-- types {{{

data VarType
    = Signed8
    | Signed16
    | Signed32
    | Signed64
    | Unsigned8
    | Unsigned16
    | Unsigned32
    | Unsigned64
    | PtrTo VarType

-- }}}

-- basic blocks {{{

data SSA g = SSA
    { ssaPhi :: [Var g]
    , ssaBody :: [Line g]
    , ssaTail :: Tail g
    }

instance FreeVars g (SSA g) where
    freeVars (SSA phi body tail) = free `withoutVars` bound
      where
        free = freeVars body <> freeVars tail
        bound = freeVars phi <> boundVars body

instance BoundVars g (SSA g) where
    boundVars (SSA phi body _) = freeVars phi <> boundVars body

instance BBlock SSA where

    bblockSucc bb = case ssaTail bb of
        Jump (Target bb' _) -> [bb']
        Branch _ (Target yes _) (Target no _) -> [yes, no]

    bblockRefs _ = []



data Line g
    = Assign (Var g) (Val g)
    | Load (Var g) (Var g)
    | Store (Var g) (Var g)

instance FreeVars g (Line g) where
    freeVars ln = case ln of
        Assign var val  -> freeVars var <> freeVars val
        Load   var addr -> freeVars [var, addr]
        Store  var addr -> freeVars [var, addr]

instance BoundVars g (Line g) where
    boundVars ln = case ln of
        Assign var _ -> singleVar var
        Load   var _ -> singleVar var
        Store  _   _ -> mempty



data Tail g
    = Jump (Target g)
    | Branch (Condition g) (Target g) (Target g)

instance FreeVars g (Tail g) where
    freeVars tl = case tl of
        Jump target -> freeVars target
        Branch cond yes no -> freeVars cond <> freeVars [yes, no]



data Target g = Target (BB g) [Var g]

instance FreeVars g (Target g) where
    freeVars (Target _ vs) = freeVars vs



data Condition g
    = NotCond (Condition g)
    | AndCond (Condition g) (Condition g)
    | OrCond  (Condition g) (Condition g)
    | IsEqual (Var g) (Var g)

instance FreeVars g (Condition g) where
    freeVars cond = case cond of
        NotCond a   -> freeVars a
        AndCond a b -> freeVars [a, b]
        OrCond  a b -> freeVars [a, b]
        IsEqual a b -> freeVars [a, b]

-- }}}

-- the monad transformer {{{

newtype SSAT g m a = SSAT { unSSAT :: StateT Int (CFGT SSA g m) a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (SSAT g) where
    lift = SSAT . lift . lift

instance (Monad m) => MonadCFG SSA g (SSAT g m) where
    cfgState = SSAT . lift . cfgState

runSSAT :: (Monad m) => (forall g. SSAT g m a) -> m a
runSSAT body = runCFGT $ evalStateT (unSSAT body) 0

class (Monad m, MonadCFG SSA g m) => MonadSSA g m | m -> g where
    freshVar :: m (Var g)

instance (Monad m) => MonadSSA g (SSAT g m) where
    freshVar = SSAT . state $ \k -> (Var k, succ k)

instance (MonadSSA g m, Monad (t m), MonadTrans t) => MonadSSA g (t m) where
    freshVar = lift freshVar

-- }}}

-- variable attributes {{{

newtype VarAttrT tag t g m a
    = VarAttrT { unVarAttrT :: StateT (IntMap t) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)

runVarAttrT :: (MonadCFG SSA g m) => tag -> VarAttrT tag t g m a -> m a
runVarAttrT _ = flip evalStateT IM.empty . unVarAttrT

class (MonadSSA g m, Tag tag t g)
        => MonadVarAttr tag t g m where
    withVarAttr :: tag -> Var g -> (Maybe t -> (a, Maybe t)) -> m a

instance (MonadSSA g m, Tag tag t g)
        => MonadVarAttr tag t g (VarAttrT tag t g m) where
    withVarAttr _ (Var k) f = VarAttrT $ do
        (x, v) <- gets $ f . IM.lookup k
        modify $ IM.alter (const v) k
        return x

instance (MonadVarAttr tag t g m, Tag tag t g, Monad (u m), MonadTrans u)
        => MonadVarAttr tag t g (u m) where
    withVarAttr tag var = lift . withVarAttr tag var

setVarAttr :: (MonadVarAttr tag t g m, Tag tag t g) => tag -> Var g -> t -> m ()
setVarAttr tag var x = withVarAttr tag var $ const ((), Just x)

getVarAttr :: (MonadVarAttr tag t g m, Tag tag t g) => tag -> Var g -> m (Maybe t)
getVarAttr tag var = withVarAttr tag var $ \v -> (v, v)

-- }}}

-- vim:fdm=marker:
