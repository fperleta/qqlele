
{-
 - qqlele/src/QQLeLe/X86.hs
 - copyright (c) 2014 Frano Perleta
 -}

-- exports {{{
module QQLeLe.X86

    -- types:
    ( Instr(..)
    , RegType(..)
    , RegName(..)
    , EffAddr(..)
    , AluOp(..)
    , Cond(..)

    -- front-end:
    , encInstr
    , encInstrBS

    -- utility functions:
    , cond
    , condNot
    , regTypeBytes

    ) where
-- }}}

-- imports {{{
import qualified Data.ByteString as BS
import           Data.ByteString (ByteString)
import           Data.Bits
import           Data.Word
-- }}}

-- instructions {{{

data Instr

    = I_nop

    -- ALU operations {{{

    -- op α:t, β:t
    -- α ← α `op` β
    | I_aluRegReg AluOp RegType RegName RegName

    -- op α:t, imm
    -- α ← α `op` imm
    | I_aluRegImm AluOp RegType RegName Word64

    -- op α:t, [addr]
    -- α ← α `op` [addr]
    | I_aluRegMem AluOp RegType RegName EffAddr

    -- op [addr], α:t
    -- [addr] ← [addr] `op` α:t
    | I_aluMemReg AluOp RegType EffAddr RegName

    -- op [addr], imm:t
    -- [addr] <- [addr] `op` imm
    | I_aluMemImm AluOp RegType EffAddr Word32

    -- }}}

    -- other operations {{{

    -- test α:t, β:t
    | I_testRegReg RegType RegName RegName

    -- test α:t, imm
    | I_testRegImm RegType RegName Word64

    -- shl α:t, imm8
    -- shr α:t, imm8
    -- rol α:t, imm8
    -- ror α:t, imm8
    | I_shiftRotImm Bool Bool RegType RegName Word8

    -- sar α:t, imm8
    | I_ashiftRightImm RegType RegName Word8

    -- not α:t
    | I_not RegType RegName

    -- neg α:t
    | I_neg RegType RegName

    -- }}}

    -- data movement {{{

    -- mov α:t, β:t
    -- α ← β
    | I_movRegReg RegType RegName RegName

    -- mov α:t, imm:t
    -- α ← imm
    | I_movRegImm RegType RegName Word64

    -- mov α:t, [addr]
    -- α ← [addr]
    | I_movRegMem RegType RegName EffAddr

    -- mov [addr], α:t
    -- [addr] ← α
    | I_movMemReg RegType EffAddr RegName

    -- mov [addr], imm:t
    -- [addr] <- imm
    | I_movMemImm RegType EffAddr Word32

    -- lea α:r64, [addr]
    | I_lea RegName EffAddr

    -- }}}

    -- flow control {{{

    -- jmp rel
    -- jcc rel
    | I_jmpRel (Maybe Cond) Word32

    -- jmp α:r64
    -- jcc α:r64
    | I_jmpReg (Maybe Cond) RegName

    -- jmp [addr]
    -- jcc [addr]
    | I_jmpMem (Maybe Cond) EffAddr

    -- call α:r64
    -- callcc α:r64
    | I_callReg (Maybe Cond) RegName

    -- call [addr]
    -- callcc [addr]
    | I_callMem (Maybe Cond) EffAddr

    -- ret k
    -- retcc k
    | I_ret (Maybe Cond) Word16

    -- }}}

  deriving (Show)



-- register types {{{

data RegType
    = R8
    | R16
    | R32
    | R64
  deriving (Show, Eq, Ord)

regTypeBytes :: (Integral a) => RegType -> a
regTypeBytes t = case t of
    R8 -> 1
    R16 -> 2
    R32 -> 4
    R64 -> 8

-- }}}

-- register names {{{

data RegName
    = RegA | RegC | RegD | RegB
    | RegSP | RegBP
    | RegSI | RegDI
    | Reg8  | Reg9
    | Reg10 | Reg11
    | Reg12 | Reg13
    | Reg14 | Reg15
  deriving (Show, Eq, Ord, Enum)

encRegName :: RegName -> Word8
encRegName = fromIntegral . fromEnum

-- }}}

-- immediate values {{{

encWord8 :: Word8 -> [Word8]
encWord8 = (:[])

encWord16 :: Word16 -> [Word8]
encWord16 k = map fromIntegral [k .&. 0xFF, k `shiftR` 8]

encWord32 :: Word32 -> [Word8]
encWord32 k = map (fromIntegral . (.&.) 0xFF) [k `shiftR` s | s <- [0, 8 .. 24]]

encWord64 :: Word64 -> [Word8]
encWord64 k = map (fromIntegral . (.&.) 0xFF) [k `shiftR` s | s <- [0, 8 .. 56]]

toSignExtByte :: [Word8] -> Maybe Word8
toSignExtByte (b:bs)
    | (testBit b 7 && all (== 0xFF) bs) || all (== 0) bs = Just b
    | otherwise = Nothing

-- }}}

-- effective addresses {{{

data EffAddr

    -- addr = disp + reg[base] + (reg[index] << scale)
    = EffAddr
        { eaDisp :: Word32
        , eaBase :: Maybe RegName
        , eaIndexShift :: Maybe (RegName, Word8)
        }

    -- addr = disp + eip/rip
    | RelAddr
        { eaDisp :: Word32
        }

  deriving (Show, Eq)

-- (scale, index, base, mod, rm, sibp, disp)
encEffAddr :: EffAddr -> (Word8, Word8, Word8, Word8, Word8, Bool, [Word8])
encEffAddr addr = case addr of

    -- [k]
    EffAddr k Nothing Nothing ->
        ( 0, 4, 5
        , 0, 4
        , True, encWord32 k
        )

    -- [base + k]
    EffAddr k (Just base) Nothing -> let
        { disp = encWord32 k
        ; (mod, disp') = case toSignExtByte disp of
            Just 0 -> (0, [])
            Just byte -> (1, [byte])
            Nothing -> (2, disp)
        ; res
            | base == RegSP || base == Reg12 =
                ( 0, 4, encRegName base
                , mod, 4
                , True, disp'
                )
            | k == 0 && (base == RegBP || base == Reg13) =
                ( 0, 0, encRegName base
                , 1, encRegName base
                , False, [0]
                )
            | otherwise =
                ( 0, 0, encRegName base
                , mod, encRegName base
                , False, disp'
                )
        } in res

    -- [(index << shift) + k]
    EffAddr k Nothing (Just (index, shift))
        | index == RegSP || index == Reg12 -> error "rsp and r12 can't be index registers"
        | otherwise ->
            ( shift, encRegName index, 5
            , 0, 4
            , True, encWord32 k
            )

    -- [base + (index << shift) + k]
    EffAddr k (Just base) (Just (index, shift)) -> let
        { disp = encWord32 k
        ; (mod, disp') = case toSignExtByte disp of
            Just 0 -> (0, [])
            Just byte -> (1, [byte])
            Nothing -> (2, disp)
        ; res
            | base == RegBP || base == Reg13 = error "rbp and r13 can't be base registers"
            | index == RegSP || index == Reg12 = error "rsp and r12 can't be index registers"
            | otherwise =
                ( shift, encRegName index, encRegName base
                , mod, 4
                , True, disp'
                )
        } in res

    RelAddr k ->
        ( 0, 0, 5
        , 0, 5
        , False, encWord32 k
        )

-- }}}

-- ALU operations {{{

data AluOp
    = AluAdd    -- 0
    | AluOr     -- 1
    | AluAdc    -- 2
    | AluSbb    -- 3
    | AluAnd    -- 4
    | AluSub    -- 5
    | AluXor    -- 6
    | AluCmp    -- 7
  deriving (Show, Eq, Ord, Enum)

encAluOp :: AluOp -> Word8
encAluOp = fromIntegral . fromEnum

-- }}}

-- conditions {{{

data Cond
    = CondO  | CondNO   -- 0, 1
    | CondC  | CondNC   -- 2, 3
    | CondZ  | CondNZ   -- 4, 5
    | CondBE | CondNBE  -- 6, 7
    | CondS  | CondNS   -- 8, 9
    | CondP  | CondNP   -- A, B
    | CondL  | CondNL   -- C, D
    | CondLE | CondNLE  -- E, F
  deriving (Show, Eq, Ord, Enum)

encCond :: Cond -> Word8
encCond = fromIntegral . fromEnum

condNot :: Cond -> Cond
condNot c = case c of
    CondO   -> CondNO;  CondNO  -> CondO
    CondC   -> CondNC;  CondNC  -> CondC
    CondZ   -> CondNZ;  CondNZ  -> CondZ
    CondBE  -> CondNBE; CondNBE -> CondBE
    CondS   -> CondNS;  CondNS  -> CondS
    CondP   -> CondNP;  CondNP  -> CondP
    CondL   -> CondNL;  CondNL  -> CondL
    CondLE  -> CondNLE; CondNLE -> CondLE

cond :: String -> Cond
cond ('n':ss) = condNot $ cond ss
cond ss = case ss of
    "o" -> CondO
    "b" -> CondC; "c" -> CondC
    "ae" -> CondNC
    "z" -> CondZ; "e" -> CondZ
    "be" -> CondBE
    "a" -> CondNBE
    "s" -> CondS
    "p" -> CondP
    "po" -> CondNP
    "l" -> CondL
    "ge" -> CondNL
    "le" -> CondLE
    "g" -> CondNLE

-- }}}

-- }}}

-- encoding {{{

encInstrBS :: Instr -> ByteString
encInstrBS = BS.pack . encInstr

encInstr :: Instr -> [Word8]
encInstr I_nop = [0x90]

-- ALU operations {{{

encInstr (I_aluRegReg op t rA rB) = opcRegReg [opc] t rA rB
  where
    opc = (encAluOp op `shiftL` 3) .|. (if t == R8 then 2 else 3)

encInstr (I_aluRegImm op t reg imm) = opcExtReg [opc] (encAluOp op) t reg imm''
  where
    imm' = take (regTypeBytes t) $ encWord64 imm
    (opc, imm'')
        | t == R8 = (0x80, imm')
        | otherwise = case toSignExtByte imm' of
            Just byte -> (0x83, [byte])
            Nothing -> (0x81, imm')

encInstr (I_aluRegMem op t reg addr) = opcRegMem [opc] t reg addr
  where
    opc = (encAluOp op `shiftL` 3) .|. (if t == R8 then 2 else 3)

encInstr (I_aluMemReg op t addr reg) = opcRegMem [opc] t reg addr
  where
    opc = (encAluOp op `shiftL` 3) .|. (if t == R8 then 0 else 1)

encInstr (I_aluMemImm op t addr imm) = opcExtMem [opc] (encAluOp op) t addr ++ imm'
  where
    imm' = take (regTypeBytes t) $ encWord32 imm
    (opc, imm'')
        | t == R8 = (0x80, imm')
        | otherwise = case toSignExtByte imm' of
            Just byte -> (0x83, [byte])
            Nothing -> (0x81, imm')

-- }}}

-- other operations {{{

encInstr (I_testRegReg t rA rB) = opcRegReg [opc] t rB rA
  where
    opc = if t == R8 then 0x84 else 0x85

encInstr (I_testRegImm t reg imm) = opcExtReg [opc] 0 t reg imm'
  where
    imm' = take (regTypeBytes $ min R32 t) $ encWord64 imm
    opc | t == R8 = 0xF6
        | otherwise = 0xF7

encInstr (I_shiftRotImm rot right t reg imm) = opcExtReg [opc] ext t reg imm'
  where
    opc =   (if imm == 1 then 0xD0 else 0xC0)
        .|. (if t == R8 then 0 else 1)
    ext = (if rot then 0 else 4) + (if right then 1 else 0)
    imm' = if imm == 1 then [] else [imm]

encInstr (I_ashiftRightImm t reg imm) = opcExtReg [opc] 7 t reg imm'
  where
    opc =   (if imm == 1 then 0xD0 else 0xC0)
        .|. (if t == R8 then 0 else 1)
    imm' = if imm == 1 then [] else [imm]

encInstr (I_not t reg) = opcExtReg [if t == R8 then 0xF6 else 0xF7] 2 t reg []

encInstr (I_neg t reg) = opcExtReg [if t == R8 then 0xF6 else 0xF7] 3 t reg []

-- }}}

-- data movement {{{

encInstr (I_movRegReg t rA rB) = opcRegReg [opc] t rA rB
  where
    opc = if t == R8 then 0x8A else 0x8B

encInstr (I_movRegImm t reg imm) = encRex t 0 0 r ++ opc : imm'
  where
    r = encRegName reg
    imm' = take (regTypeBytes t) $ encWord64 imm
    opc = (if t == R8 then 0xB0 else 0xB8) + (r .&. 0x7)

encInstr (I_movRegMem t reg addr) = opcRegMem [opc] t reg addr
  where
    opc = if t == R8 then 0x8A else 0x8B

encInstr (I_movMemReg t addr reg) = opcRegMem [opc] t reg addr
  where
    opc = if t == R8 then 0x88 else 0x89

encInstr (I_movMemImm t addr imm) = opcExtMem [opc] 0 t addr ++ imm'
  where
    opc = if t == R8 then 0xC6 else 0xC7
    imm' = take (regTypeBytes t) $ encWord32 imm

encInstr (I_lea reg addr) = opcRegMem [0x8D] R64 reg addr

-- }}}

-- flow control {{{

encInstr (I_jmpRel Nothing rel) = 0xE9 : encWord32 rel
encInstr (I_jmpRel (Just cc) rel) = 0x0F : (0x80 + encCond cc) : encWord32 rel

encInstr (I_jmpReg mcc reg) = skipWrap mcc $ opcExtReg [0xFF] 4 R32 reg []

encInstr (I_jmpMem mcc addr) = skipWrap mcc $ opcExtMem [0xFF] 4 R32 addr

encInstr (I_callReg mcc reg) = skipWrap mcc $ opcExtReg [0xFF] 2 R32 reg []

encInstr (I_callMem mcc addr) = skipWrap mcc $ opcExtMem [0xFF] 2 R32 addr

encInstr (I_ret mcc k) = skipWrap mcc $ case k of
    0 -> [0xC3]
    _ -> 0xC2 : encWord16 k

-- }}}



-- instruction parts {{{

encRex :: RegType -> Word8 -> Word8 -> Word8 -> [Word8]
encRex t r x b
    | rex == 0x40 = if t == R8 then [0x40] else []
    | otherwise = [rex]
  where
    rex = 0x40
        .|. (if t == R64 then 0x8 else 0)
        .|. ((r .&. 0x8) `shiftR` 1)
        .|. ((x .&. 0x8) `shiftR` 2)
        .|. ((b .&. 0x8) `shiftR` 3)

encModRM :: Word8 -> Word8 -> Word8 -> Word8
encModRM mod reg rm
    =   (mod `shiftL` 6)
    .|. ((reg .&. 0x7) `shiftL` 3)
    .|. (rm .&. 0x7)

encSIB :: Word8 -> Word8 -> Word8 -> Word8
encSIB s x b
    =   (s `shiftL` 6)
    .|. ((x .&. 0x7) `shiftL` 3)
    .|. (b .&. 0x7)

-- }}}

-- templates {{{

opcRegReg :: [Word8] -> RegType -> RegName -> RegName -> [Word8]
opcRegReg opc t rA rB = concat
    [ if t == R16 then [0x66] else []
    , encRex t kA 0 kB
    , opc
    , [encModRM 3 kA kB]
    ]
  where
    kA = encRegName rA
    kB = encRegName rB

opcExtReg :: [Word8] -> Word8 -> RegType -> RegName -> [Word8] -> [Word8]
opcExtReg opc ext t reg rest = concat
    [ if t == R16 then [0x66] else []
    , encRex t 0 0 r
    , opc
    , [encModRM 3 ext r]
    , rest
    ]
  where
    r = encRegName reg

opcRegMem :: [Word8] -> RegType -> RegName -> EffAddr -> [Word8]
opcRegMem opc t reg addr = concat
    [ if t == R16 then [0x66] else []
    , encRex t r x b
    , opc
    , [encModRM mod r rm]
    , sib
    , disp
    ]
  where
    r = encRegName reg
    sib = if sibp then [encSIB s x b] else []
    (s, x, b, mod, rm, sibp, disp) = encEffAddr addr

opcExtMem :: [Word8] -> Word8 -> RegType -> EffAddr -> [Word8]
opcExtMem opc ext t addr = concat
    [ if t == R16 then [0x66] else []
    , encRex t 0 x b
    , opc
    , [encModRM mod ext rm]
    , sib
    , disp
    ]
  where
    sib = if sibp then [encSIB s x b] else []
    (s, x, b, mod, rm, sibp, disp) = encEffAddr addr

-- }}}

-- skips {{{

skipInstr :: Cond -> [Word8] -> [Word8]
skipInstr cc code = (0x70 + encCond cc) : encWord8 (toEnum $ length code)

skipWrap :: Maybe Cond -> [Word8] -> [Word8]
skipWrap mcc code = case mcc of
    Just cc -> skipInstr (condNot cc) code ++ code
    Nothing -> code

-- }}}

-- }}}

-- vim:fdm=marker:
