
{-
 - qqlele/src/QQLeLe/Asm.hs
 - copyright (c) 2014 Frano Perleta
 -}

-- extensions {{{
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes #-}
-- }}}

-- exports {{{
module QQLeLe.Asm

    -- labels
    ( Label()

    -- the monad
    , Asm()
    , runAsm
    , execAsm

    -- primitives
    , here
    , forward
    , label
    , chunk
    , relative

    ) where
-- }}}

-- imports {{{
import           Control.Applicative
import           Control.Monad.State
import qualified Data.ByteString as BS
import           Data.ByteString (ByteString)
import qualified Data.IntMap.Strict as IM
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntSet as IS
import           Data.IntSet (IntSet)
import           Data.Word

import           QQLeLe.X86
-- }}}

-- labels {{{

newtype Label asm = Label { unLabel :: Int }
  deriving (Eq, Ord)

-- }}}

-- tape {{{

data Tape asm = Tape
    { tapeLabels :: IntSet
    , tapeBefore :: Before asm
    , tapeAfter :: After asm
    }

data Before asm
    = BeginTape
    | SnocTape (Before asm) (Chunk asm)
        IntSet

data After asm
    = EndTape
    | ConsTape (Chunk asm) (After asm)
        IntSet

data Chunk asm
    = Chunk [Instr]
    | Relative (Label asm) (Word32 -> Instr)

tapeEmpty :: Tape asm
tapeEmpty = Tape IS.empty BeginTape EndTape

tapeBck, tapeFwd :: Tape asm -> Maybe (Tape asm)
tapeBck (Tape _ BeginTape _) = Nothing
tapeBck (Tape l (SnocTape b ch l') a) = Just $ Tape l' b (ConsTape ch a l)
tapeFwd  (Tape _ _ EndTape) = Nothing
tapeFwd  (Tape l b (ConsTape ch a l')) = Just $ Tape l' (SnocTape b ch l) a

tapeRewind :: Tape asm -> Tape asm
tapeRewind tp = case tapeBck tp of
    Just tp' -> tapeRewind tp'
    Nothing -> tp

tapeSeekBck, tapeSeekFwd :: Label asm -> Tape asm -> Maybe (Tape asm)
(tapeSeekBck, tapeSeekFwd) = (go tapeBck, go tapeFwd)
  where
    go step l@(Label n) tp
        | n `IS.member` tapeLabels tp = Just tp
        | otherwise = step tp >>= go step l

tapeInsert :: Chunk asm -> Tape asm -> Tape asm
tapeInsert ch tp = tp
    { tapeLabels = IS.empty
    , tapeBefore = SnocTape (tapeBefore tp) ch (tapeLabels tp)
    }

tapeRead :: Tape asm -> Maybe (Chunk asm, Tape asm)
tapeRead (Tape _ _ EndTape) = Nothing
tapeRead (Tape l b (ConsTape ch a l')) = Just (ch, Tape l' (SnocTape b ch l) a)

-- }}}

-- the monad {{{

data AsmState asm = AsmState
    { asmTape :: Tape asm
    , asmNext :: {-# UNPACK #-} !Int
    , asmFwdRefs :: IntSet
    }

initAsmState = AsmState tapeEmpty 0 IS.empty

newtype Asm asm a = Asm { unAsm :: State (AsmState asm) a }
  deriving (Functor, Applicative, Monad)



here :: Asm asm (Label asm)
here = Asm . state $ \(as@AsmState{asmTape = tp, asmNext = n}) ->
    case IS.minView $ tapeLabels tp of
        Just (n, _) -> (Label n, as)
        Nothing -> (Label n, as { asmTape = tp {tapeLabels = IS.singleton n}, asmNext = succ n })

forward :: Asm asm (Label asm)
forward = Asm . state $ \(as@AsmState{asmNext = n, asmFwdRefs = fs}) ->
    (Label n, as { asmNext = succ n, asmFwdRefs = IS.insert n fs })

label :: Label asm -> Asm asm ()
label l@(Label n) = Asm . modify $ \(as@AsmState{asmTape = tp, asmFwdRefs = fs}) ->
    if IS.member n fs
    then as { asmTape = tp {tapeLabels = IS.insert n $ tapeLabels tp}, asmFwdRefs = IS.delete n fs }
    else error "cannot place the same label at multiple location"

chunk :: [Instr] -> Asm asm ()
chunk ins = Asm . modify $ \as -> case asmTape as of
    tp -> as { asmTape = tapeInsert (Chunk ins) tp }

relative :: Label asm -> (Word32 -> Instr) -> Asm asm ()
relative l f = Asm . modify $ \as -> case asmTape as of
    tp -> as { asmTape = tapeInsert (Relative l f) tp }

-- }}}

-- multipass assembler {{{

runAsm :: Int -> (forall asm. Asm asm a) -> (a, Maybe ByteString)
runAsm maxPasses body = case runState (unAsm body) initAsmState of
    (x, as) -> let
        { tp = tapeRewind $ asmTape as
        ; go 0 _ = (x, Nothing)
        ; go n lm = case pass lm tp of
            (lm', trace)
                | lm == lm' -> (x, Just . BS.concat $ reverse trace)
                | otherwise -> go (pred n) lm'
        } in go maxPasses IM.empty

execAsm :: Int -> (forall asm. Asm asm a) -> Maybe ByteString
execAsm maxPasses body = snd $ runAsm maxPasses body

pass :: IntMap Word32 -> Tape asm -> (IntMap Word32, [ByteString])
pass = go (0 :: Word32) []
  where
    go :: Word32 -> [ByteString] -> IntMap Word32 -> Tape asm -> (IntMap Word32, [ByteString])
    go offs trace lm tp = let
        { lm' = IM.fromSet (const offs) (tapeLabels tp) `IM.union` lm
        ; (offs', trace') = case tapeRead tp of
            Just (Chunk is, _) -> let
                { ins = BS.concat (map encInstrBS is)
                ; len = toEnum $ BS.length ins
                } in (len + offs, ins : trace)
            Just (Relative (Label n) f, _) -> let
                { loc = IM.findWithDefault 0 n lm'
                ; len0 = toEnum . length . encInstr $ f 0x55555555
                ; ins = encInstrBS . f $ loc - offs - len0
                ; len = toEnum $ BS.length ins
                ; ins' = encInstrBS . f $ loc - offs - len
                ; len' = toEnum $ BS.length ins'
                } in (len' + offs, ins' : trace)
            Nothing -> (offs, trace)
        } in case tapeRead tp of
            Just (_, tp') -> go offs' trace' lm' tp'
            Nothing -> (lm', trace')

-- }}}

-- vim:fdm=marker:
