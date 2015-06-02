{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, PatternSynonyms, ViewPatterns, TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
module UnionPay.Types where

import Data.Int
import Data.Word
import Data.Bits
import Data.String
import Data.Functor
import Data.Hex
import System.IO.Unsafe
import Control.Applicative
import qualified Data.ByteString.Lazy as B
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.Monoid
import Control.Monad

type Byte   = Word8
type BS     = B.ByteString
-------------------APDU 定义 和IC卡交互的最底层数据结构-------------------------------------
data C_APDU = C_APDU !Word8 !Word8 !Word8 !Word8 !(Maybe BS) !(Maybe Word8)  --request
data R_APDU = R_APDU !BS !Word8 !Word8           -- response , bytestring may be empty
    deriving (Show)

pattern R_SUCCESS bs = R_APDU bs 0x90 0x00      -- 成功
pattern R_Locked <- R_APDU _ 0x6A 0x81
pattern R_FileNotFound <- R_APDU _ 0x6A 0x82
pattern R_6A83 <- R_APDU _ 0x6A 0x83
pattern R_NotSupport <- R_APDU _ 0x69 0x85

encodeC_APDU :: C_APDU -> BS
encodeC_APDU (C_APDU cla ins p1 p2 mbody mle) = runPut $ do
    put cla >> put ins >> put p1 >> put p2
    case mbody of
        Just body -> putWord8 (fromIntegral $ B.length body) >> putLazyByteString body
        _ -> return ()
    case mle of
        Just le -> put le
        _ -> return ()

decodeR_APDU :: BS -> R_APDU
decodeR_APDU bs
    | Just (bs', sw2) <- B.unsnoc bs, Just (bs'', sw1) <- B.unsnoc bs' = R_APDU bs'' sw1 sw2
    | otherwise = error "decode R_APDU ERROR,no enough bytes"

unknownError :: R_APDU -> a
unknownError (R_APDU _ e1 e2) = error $ "其他错误 unknown R_APDU error:" ++ show e1 ++ "," ++ show e2

class IsC_APDU a where
    toC_APDU :: a -> C_APDU

class FromR_APDU a where
    fromR_APDU :: R_APDU -> a
------------------------------------BLE TLV 定义----------------------------
data TAG = TAG1 !Word8 | TAG2 !Word8 !Word8
instance Show TAG where
    show (TAG1 w1) = unwords ["TAG1", showHex w1]
    show (TAG2 w1 w2) = unwords ["TAG2", showHex w1 ++ showHex w2]

instance Binary TAG where
    put (TAG1 w) = putWord8 w
    put (TAG2 w1 w2) = putWord8 w1 >> putWord8 w2
    get = do
        w <- getWord8
        if w .&. 0x1F == 0x1F then TAG2 w <$> getWord8 else return $ TAG1 w

newtype Length = Length Int64     deriving (Show)
instance Binary Length where
    put (Length len)
        | len < 128 = putWord8 $ fromIntegral len
        | len < fromIntegral (maxBound :: Int16) = putWord8 0x82 >> put (fromIntegral len :: Int16)

    get = do
        w <- getWord8
        let len
                | testBit w 7 = do
                    let size = fromIntegral $ w .&. 0x0F
                    bs <- replicateM size getWord8
                    return $ foldl (\i w -> shift i 8 + fromIntegral w) (0 :: Int64) bs
                | otherwise = return $ fromIntegral w
        Length <$> len

type VALUE = BS
data BleTLV = TLVSimple TAG VALUE
            | TLVCompose TAG [BleTLV]
     deriving (Show)
pattern S1 w bs = TLVSimple (TAG1 w) bs
pattern S2 w1 w2 bs = TLVSimple (TAG2 w1 w2) bs
pattern C1 w bs = TLVCompose (TAG1 w) bs
pattern C2 w1 w2 bs = TLVCompose (TAG2 w1 w2) bs

pattern Language bs = S2 0x5F 0x2D bs       -- 首选语言
pattern BankCode w  <- S2 0x9F 0x11 (B.head -> w)    -- 发卡行代码表索引
pattern BankData bs = C2 0xBF 0x0C bs       -- 发卡行自定义数据

tag :: BleTLV -> TAG
tag (TLVSimple s _) = s
tag (TLVCompose s _) = s

instance Binary BleTLV where
    put (TLVSimple s bs) = do
        put s
        put $ Length $ B.length bs
        put bs
    put (TLVCompose s vs) = do
        put s
        let bs = mconcat $ map encode vs
        put $ Length $ B.length bs
        put bs

    get = do
        t <- get
        Length len <- get
        bs <- getLazyByteString len
        return $ if isComposeTag t then TLVCompose t (decodeMany bs) else TLVSimple t bs
        where
            isComposeTag tag = let ww = case tag of
                                    TAG1 w -> w
                                    TAG2 w _ -> w
                               in testBit ww 5

class FromBleTLV a where
    fromBleTLV :: BleTLV -> Maybe a

fromBleTLVs :: (BleTLV -> a -> a) -> [BleTLV] -> a -> a
fromBleTLVs f vs a = foldr ($) a $ map f vs

--------------------------IC Command 定义---------------------------------------------
newtype DDF = DDF Word8        -- | sfi  目录定义文件（Directory Definition File）
    deriving (Show)
instance FromBleTLV DDF where
    fromBleTLV (TLVCompose _ vs) = Just $ head [DDF $ B.head bs | C1 0xA5 vs' <- vs, S1 0x88 bs <- vs']
    fromBleTLV _ = Nothing

instance FromR_APDU (Maybe DDF) where
    fromR_APDU rsp = case rsp of
        R_SUCCESS bs   -> fromBleTLV $ decode bs        -- 成功
        R_FileNotFound -> Nothing        -- IC卡上没有PSE
        R_Locked       -> error "卡被锁定或者选择（SELECT）命令不支持 4-card locked or command not support"
        R_6A83         -> error "PSE被锁定 5-PSE locked"
        _              -> unknownError rsp

-- | 选择命令(通过名称选择)
data SelectCmd = SelectCmd BS
instance IsC_APDU SelectCmd where
    toC_APDU (SelectCmd file) = C_APDU 0x00 0xA4 0x04 0x00 (Just file) (Just 0x00)

data ReadCmd = ReadCmd DDF Word8      -- ^ sfi idx
instance IsC_APDU ReadCmd where
    toC_APDU (ReadCmd (DDF sfi) idx) = C_APDU 0x00 0xB2 idx (shift sfi 3 .|. 0x04) Nothing (Just 0x00)

data App = App {
    aid :: BS             -- aid
  , appLabel :: BS        -- label
  , appPriority :: Word8            -- priority
} deriving (Eq, Show)

instance Ord App where compare (App _ _ p1) (App _ _ p2) = compare p1 p2
instance FromBleTLV App where
    fromBleTLV (C1 0x61 vs) = Just $ fromBleTLVs f vs $ App{appPriority=0}
        where
            f (S1 0x4F bs) app = app{aid=bs}
            f (S1 0x50 bs) app = app{appLabel=bs}
            f (S1 0x87 bs) app = app{appPriority=B.head bs}
    fromBleTLV _ = Nothing

type DO = (TAG, Length)         -- 数据对象  卡片需要的参数对象
type DOL = [DO]                 -- 数据对象列表
decodeDOL = runGet $ go []
    where
        getItem = do
            tag :: TAG <- get
            length :: Length <- get
            return (tag, length)
        go rs = do
            e <- isEmpty
            if e then return rs else do
                item <- getItem
                go $ rs ++ [item]

data AppInfo = AppInfo {
    appLan :: BS          -- 语言
  , bankCode :: Word8               -- 发卡行代码索引 bankCode
  , pdol   :: DOL                   -- PDOL
  , bankData :: [BleTLV]            -- 发卡行自定义数据 bankData
} deriving (Show)

instance FromBleTLV AppInfo where
    fromBleTLV (TLVCompose _ vs) = Just $ fromBleTLVs f sub $ AppInfo undefined undefined undefined undefined
        where
            sub = head [ vs' | C1 0xA5 vs' <- vs]
            f (Language bs) appInfo = appInfo{appLan=bs}
            f (BankCode bs) appInfo = appInfo{bankCode=bs}
            f (S2 0x9F 0x38 bs) appInfo = appInfo{pdol=decodeDOL bs}
            f (BankData bs) appInfo = appInfo{bankData=bs}
            f _ appInfo = appInfo           -- ??
    fromBleTLV _ = Nothing

instance FromR_APDU (Maybe AppInfo) where
    fromR_APDU rsp = case rsp of
        R_SUCCESS bs -> fromBleTLV $ decode bs        -- 成功
        R_Locked       -> error "应用被锁定 6-app locked"
        R_FileNotFound       -> Nothing        -- IC卡上没有PSE
        R_6A83       -> error "PSE被锁定 5-PSE locked"
        _            -> unknownError rsp

data GPOCmd = GPOCmd BS           -- Get Processing Options命令
instance IsC_APDU GPOCmd where
    toC_APDU (GPOCmd bs) = C_APDU 0x80 0xA8 0x00 0x00 (Just ds) (Just 0x00)
        where ds = mappend (B.pack [0x83, fromIntegral $ B.length bs]) bs

-- | 交易日志
data TranRecord = TranRecord {
    tranData :: BS    -- 交易日期
  , tranTime :: BS    -- 交易时间
  , tranMoney :: BS   -- 授权金额
  , otherMoney :: BS  -- 其他金额
  , country    :: Word16        -- 终端国家代码
  , currency   :: Word16        -- 交易货币代码
  , merchant   :: BS  -- 商户名称
  , tranType   :: Word8         -- 交易类型
  , tranAtc        :: Word16        -- 应用交易计数器（ATC）
}

decodeTranRecord :: BS -> TranRecord
decodeTranRecord = runGet $ do
    tranData <- getLazyByteString 3
    tranTime <- getLazyByteString 3
    tranMoney <- getLazyByteString 6
    otherMoney <- getLazyByteString 6
    country  <- getWord16be
    currency <- getWord16be
    merchant <- getLazyByteString 20
    tranType <- getWord8
    atc      <- getWord16be
    return TranRecord{..}

data GetDataCmd = GetDataCmd TAG        -- 取数据命令
instance IsC_APDU GetDataCmd where
    toC_APDU (GetDataCmd (TAG2 w1 w2)) = C_APDU 0x80 0xCA w1 w2 Nothing (Just 0x00)

data GenerateACCmd = GenerateACCmd ACType BS          -- 生成应用密文（GENERATE AC）命令
instance IsC_APDU GenerateACCmd where
    toC_APDU (GenerateACCmd acType bs) = C_APDU 0x80 0xAE (acTypeWord acType) 0x00 (Just bs) (Just 0x00)
        where
            acTypeWord :: ACType -> Word8
            acTypeWord t = case t of
                AAC  -> 0x00
                TC   -> 0x40
                ARQC -> 0x80

data ExteneralAuthorize = ExteneralAuthorize BS           -- 外部认证（EXTERNAL AUTHENTICATE）命令
instance IsC_APDU ExteneralAuthorize where
    toC_APDU (ExteneralAuthorize bs) = C_APDU 0x00 0x82 0x00 0x00 (Just bs) Nothing

-- 应用初始化
data AEF = AEF Word8 Word8 Word8 Word8          -- sfi start end xx
    deriving (Show)
data TradeOption = TradeOption Word8 [AEF]                    -- aip afl
    deriving (Show)

supportSDA, supportDDA, supportCVM, supportTRM, supportBV, supportCDA :: TradeOption -> Bool
supportSDA (TradeOption w _) = testBit w 6      -- 卡片支持SDA，静态脱机认证
supportDDA (TradeOption w _) = testBit w 5      -- 卡片支持DDA，动态脱机认证
supportCVM (TradeOption w _) = testBit w 4      -- 卡片支持持卡人认证
supportTRM (TradeOption w _) = testBit w 3      -- 卡片支持终端风险管理
supportBV  (TradeOption w _) = testBit w 2      -- 卡片支持发卡行认证
supportCDA (TradeOption w _) = testBit w 0      -- 卡片支持CDA，复合脱机认证

decodeTradeOption :: BS -> TradeOption
decodeTradeOption = runGet $ do
    w <- getWord8
    getWord8
    afls <- getMany getAEF
    return $ TradeOption w afls
    where
        getAEF = do
            sfi <- getWord8
            AEF (shiftR sfi 3) <$> get <*> get <*> get

instance FromR_APDU TradeOption where
    fromR_APDU rsp = case rsp of
        R_SUCCESS (decode -> S1 0x80 vs) -> decodeTradeOption vs
        R_NotSupport -> error "GPO.getOption: trade not support"
        _            -> unknownError rsp

data ACType = AAC | TC | ARQC   deriving (Show)
-- 交易定义
data Trade = Trade {
    tradeType :: Word8          -- 交易类型
  , amount :: Integer           -- 交易金额
  , date   :: BS            -- 交易日期，格式yyMMdd BCD编码 length 3
  , time   :: BS            -- 交易时间，格式HHmmss
  , magic  :: Word32            -- 交易随机数，用来防止伪造数据
  , authorizeCode :: BS     -- 授权码
  , acType  :: ACType           -- 应用密文类型
  , tradeMerchant :: BS     -- 商户名称
}   deriving (Show)

-- 生成应用初始化所需要的PDOL数据
class HasDOLData a where
    generateDO :: a -> DO -> Maybe BS

instance HasDOLData Trade where
    generateDO Trade{..} (tag, len) = case tag of
        TAG2 0x9F 0x02  -> Just $ intToBS 12 amount            --  交易金额，BCD编码
        TAG2 0x9F 0x03  -> Just $ intToBS 12 0            -- 其他金额，BCD编码
        TAG1 0x9A       -> Just date    -- 交易日期
        TAG1 0x9C       -> Just $ B.singleton tradeType     -- 交易类型
        TAG2 0x9F 0x37  -> Just $ encode magic                       -- 交易模数
        TAG2 0x9F 0x21  -> Just time                        -- 交易时间
        TAG2 0x9F 0x4E  -> Just tradeMerchant                   -- 商户名称
        TAG1 0x8A       -> Just authorizeCode               -- 授权码
        _               -> Nothing

-- 卡片信息
data Card = Card {
    track2      :: BS         -- 磁条2信息
  , panSeq      :: BS         -- 应用主账号序列号
  , bankPubKey  :: BS         -- 发卡行公钥证书
  , bankPubKeyLeft  :: BS     -- 发卡行公钥余数
  , bankPubKeyPower :: BS       -- 发卡行公钥指数
  , icPubKey        :: BS       -- IC卡公钥证书
  , icPubKeyLeft    :: BS       -- IC卡公钥余数
  , icPubKeyPower   :: BS       -- IC卡公钥指数
  , cardIDInfos     :: BS       -- 产品标识信息
  , pki             :: BS       -- CA公钥索引
  , ddol            :: BS       -- 动态数据认证数据对象列表（DDOL）
  , serviceCode     :: BS       -- 服务代码
  , sad             :: BS       -- 签名的静态应用数据（SAD）
  , cvm             :: BS       -- 持卡人验证方法（CVM）列表
  , defaultIAC      :: BS       -- 发卡行行为代码（IAC）-缺省
  , rejectIAC       :: BS       -- 发卡行行为代码（IAC）-拒绝
  , onlineIAC       :: BS       -- 发卡行行为代码（IAC）-联机
  , createDate      :: BS       -- 应用生效日期, 格式yyMMdd
  , expireDate      :: BS       -- 应用失效日期, 格式yyMMdd
  , pan             :: BS       -- 主Pan
  , version         :: BS       -- 应用版本号
  , auc             :: BS       -- 应用用途控制
  , cdol1           :: DOL       -- 卡片风险管理数据对象列表1（CDOL1）
  , cdol2           :: DOL       -- 卡片风险管理数据对象列表2（CDOL2）
  , offlineTradeDown:: Int       -- 连续脱机交易下限
  , offlineTradeUp  :: Int      -- 连续脱机交易上限
} deriving (Show)

-- 电子现金
data ECash = ECash {
    ecashBalance    :: Integer   -- 电子现金(分)
  , ecashBalanceLimit   :: Integer   -- 电子现金上限(分)
}  deriving (Show)

defaultCard :: Card
defaultCard = Card {offlineTradeDown = -1, offlineTradeUp = -1, cardIDInfos=B.empty}

setCardInfo :: BleTLV -> Card -> Card
setCardInfo tlv card = case tlv of
    S1 0x57 bs -> card{track2=bs}
    S2 0x5F 0x34 bs -> card{panSeq=bs}
    S1 0x90 bs      -> card{bankPubKey=bs}
    S1 0x92 bs      -> card{bankPubKeyLeft=bs}
    S2 0x9F 0x32 bs -> card{bankPubKeyPower=bs}
    S2 0x9F 0x46 bs -> card{icPubKey=bs}
    S2 0x9F 0x48 bs -> card{icPubKeyLeft=bs}
    S2 0x9F 0x47 bs -> card{icPubKeyPower=bs}
    S2 0x9F 0x63 bs -> card{cardIDInfos=bs}
    S1 0x8F bs      -> card{pki=bs}
    S2 0x9F 0x49 bs -> card{ddol=bs}
    S2 0x5F 0x30 bs -> card{serviceCode=bs}
    S1 0x93 bs      -> card{sad=bs}
    S1 0x8E bs      -> card{cvm=bs}
    S2 0x9F 0x0D bs -> card{defaultIAC=bs}
    S2 0x9F 0x0E bs -> card{rejectIAC=bs}
    S2 0x9F 0x0F bs -> card{onlineIAC=bs}
    S2 0x5F 0x25 bs -> card{createDate=bs}
    S2 0x5F 0x24 bs -> card{expireDate=bs}
    S1 0x5A bs      -> card{pan=bs}
    S2 0x9F 0x08 bs -> card{version=bs}
    S2 0x9F 0x07 bs -> card{auc=bs}
    S1 0x8C bs      -> card{cdol1=decodeMany bs}
    S1 0x8D bs      -> card{cdol2=decodeMany bs}
    S2 0x9F 0x14 bs -> card{offlineTradeDown=getInt bs}
    S2 0x9F 0x23 bs -> card{offlineTradeUp=getInt bs}
    S1 0x84 bs      -> card
    _               -> card
    where
        getInt :: BS -> Int
        getInt = fromIntegral . B.head

-- 应用密文对象，是GenerateAC命令的产物
data AC = AC {
    cid :: Byte
  , atc :: Word16
  , ac  :: Word64       -- 8 byte
  , bankDatas   :: BS
} deriving (Show)

decodeAC :: BS -> AC
decodeAC = runGet $ do
    cid <- get
    atc <- get
    ac  <- get
    bankDatas <- getRemainingLazyByteString
    return $ AC{..}

----------------------------------internal utility--------------------------------
-- 重复多次decode，直到所有数据全部解析
getMany :: Get a -> Get [a]
getMany f = go []
    where
        go rs = do
            e <- isEmpty
            if e then return rs else do
                item <- f
                go $ rs ++ [item]

decodeMany :: Binary a => BS -> [a]
decodeMany = runGet $ getMany get

-- BCD 编码
{-# NOINLINE intToBS #-}
intToBS :: Int -> Integer -> BS
intToBS len i = let s = show i
                    pad
                        | length s < len  = replicate (len - length s) '0'
                        | otherwise         = ""
                in unsafePerformIO $ unhex $ fromString $ pad <> s

bsToInt :: BS -> Integer
bsToInt = read . init . tail . show . hex

class ShowHex a where
    showHex :: a -> String

toHex :: (Bits a, Integral a) => [a] -> String
toHex = map (\i -> "0123456789ABCDEF" !! (fromIntegral $ i .&. 0x0F))

instance ShowHex Word8  where    showHex w = toHex [shiftR w 4, w]
instance ShowHex Word16 where    showHex w = toHex $ map (shiftR w) [12, 8..0]
instance ShowHex Word32 where    showHex w = toHex $ map (shiftR w) [28, 24..0]
instance ShowHex Word64 where    showHex w = toHex $ map (shiftR w) [60, 56..0]