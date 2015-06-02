-- 银联PBOC3.0实现
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module UnionPay.PBOC3 where

import Data.Monoid
import Data.Maybe
import Data.Int
import Data.Bits
import Data.String
import Data.Hex
import Data.Functor
import qualified Data.ByteString.Lazy as B
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Control.Monad

import UnionPay.Transfer
import UnionPay.Types

transferCmd :: IsC_APDU a => Transfer -> a -> IO R_APDU
transferCmd Transfer{..} req = do
    bs <- transfer $ encodeC_APDU $ toC_APDU req
    return $ decodeR_APDU bs

-- | 选择文件
selectDDF :: Transfer -> BS -> IO (Maybe DDF)
selectDDF handle file = fromR_APDU <$> transferCmd handle (SelectCmd file)

-- | 选择应用
selectADF :: Transfer -> BS -> IO (Maybe AppInfo)
selectADF handle aid = fromR_APDU <$> transferCmd handle (SelectCmd aid)

-- | 读取记录
readRecord :: Transfer -> DDF -> Word8 -> IO (Maybe BleTLV)
readRecord handle ddf idx = do
    rsp <- transferCmd handle $ ReadCmd ddf idx
    return $ case rsp of
        R_SUCCESS bs -> Just $ decode bs
        R_6A83       -> Nothing               -- 读到最后一条记录
        _            -> unknownError rsp

-- | 从1开始读取所有记录
readAllRecords :: Transfer -> DDF -> IO [BleTLV]
readAllRecords handle ddf = go 1 []
    where
        go idx rs = do
            mr <- readRecord handle ddf idx
            case mr of
                Just r -> go (idx+1) $ r:rs
                Nothing -> return rs

-- | Get Processing Options命令
getOption :: Transfer -> BS -> IO TradeOption
getOption handle bs = fromR_APDU <$> transferCmd handle (GPOCmd bs)

readTranRecord handle idx = do
    let ddf = DDF 11
    rsp <- transferCmd handle $ ReadCmd ddf idx
    case rsp of
        R_SUCCESS bs -> return $ Just $ decodeTranRecord bs
        _            -> return Nothing

-- | 取数据（GET DATA）命令
getData :: Transfer -> TAG -> IO (Maybe BS)
getData handle tag = do
    rsp <- transferCmd handle $ GetDataCmd tag
    case rsp of
        R_SUCCESS bs -> return $ Just $ bs
        R_APDU _ 0x6A 0x88 -> return Nothing
        _            -> unknownError rsp

-- | 生成应用密文（GENERATE AC）命令
generateAC :: Transfer -> ACType -> BS -> IO BleTLV
generateAC handle acType bs = do
    rsp <- transferCmd handle $ GenerateACCmd acType bs
    case rsp of
        R_SUCCESS bs -> return $ decode bs
        _            -> unknownError rsp

-- | 外部认证（EXTERNAL AUTHENTICATE）命令
exteneralAuthorize :: Transfer -> BS -> IO Bool
exteneralAuthorize handle bs = do
    rsp <- transferCmd handle $ ExteneralAuthorize bs
    case rsp of
        R_SUCCESS _ -> return True
        R_APDU _ 0x63 0x00 -> return False      -- 验证失败
        R_APDU _ 0x69 0x85 -> return False      -- 已经收到过验证数据
        _           -> return False             -- 其他错误

-- 支付系统环境（Payment System Environment）
pse :: BS
pse = "1PAY.SYS.DDF01"

------------------------------------PBOC借贷记 交易流程-----------------------------------
----------终端对象------------
data Terminal = Terminal {
    supportAIDs :: [BS]             -- hex编码！
  , appVersion  :: BS
  , eci         :: Word8            -- 电子现金的指示器
  , edf         :: Word8
  , ttr         :: Word32     -- 终端交易属性
  , tsi         :: Word8            -- 终端控制信息
  , tvr         :: BS               -- length 5
  , country     :: Word16           -- 国家代码
  , currency    :: Word16           -- 币种代码
}

defaultTerminal = Terminal {
    supportAIDs = ["A0000003330101"]
  , eci = 0x01
  , edf = 0x00
  , ttr = 0x54800000
  , tsi = 0x00
  , tvr = B.replicate 5 0x00
  , country = 0x0156
  , currency = 0x0156
}

instance HasDOLData Terminal where
    generateDO Terminal{..} (tag, len) = case tag of
        TAG2 0x9F 0x7A  ->  Just $ B.singleton eci
        TAG2 0x9F 0x66  ->  Just $ encode ttr
        TAG2 0x9F 0x1A  ->  Just $ encode country
        TAG1 0x95       ->  Just tvr
        TAG2 0x5F 0x2A  ->  Just $ encode currency
        TAG2 0xDF 0x60  ->  Just $ B.singleton edf
        _               ->  Nothing

readCardSupportApps :: Transfer -> IO [App]
readCardSupportApps handle = do
    mddf <- selectDDF handle pse    -- 建立支付系统环境并进入初始目录
    case mddf of
        Just ddf -> do
            vs <- readAllRecords handle ddf
            return [ app :: App | TLVCompose _ vv <- vs, app <- mapMaybe fromBleTLV vv]
        Nothing -> do
                let aids = []
                return aids

-- | PBOC借贷记，第一步：应用选择
selectApp :: Transfer -> Terminal -> IO (Maybe AppInfo)
selectApp handle Terminal{..} = do
    cardSupportApps <- readCardSupportApps handle
    when (null cardSupportApps) $ fail "no PSE in IC card"
    let apps = [ app | app@(App aid _ _) <- cardSupportApps, aid' <- supportAIDs, B.isPrefixOf aid' (hex aid)]
    when (null apps) $ fail "no app can use"       -- 没有应用可供选择，流程终止
    -- 选择优先级数字最小的应用
    let App aid _ _ = minimum apps
    selectADF handle aid

generateDOL fs = mconcat . map f
    where   f obj = head $ mapMaybe ($ obj) fs

readAEF handle card (AEF sfi start end _)
    | start <= end = do
        mvs <- mapM (readRecord handle $ DDF sfi) [start..end]
        return $ fromBleTLVs setCardInfo [tlv | TLVCompose _ vs' <- catMaybes mvs, tlv <- vs'] card
    | otherwise = return card

-- | PBOC借贷记，第二步：应用初始化
initApp :: Transfer -> AppInfo -> Terminal -> Trade -> IO Card
initApp handle AppInfo{..} terminal trade = do
    TradeOption aip afl <- getOption handle $ generateDOL [generateDO terminal, generateDO trade] pdol
    foldM (readAEF handle) defaultCard afl

-- 读取电子现金余额及上限
readECash :: Transfer -> IO ECash
readECash handle = do
    Just (decode -> S2 0x9F 0x79 bs1) <- getData handle $ TAG2 0x9F 0x79     -- 电子现金余额
    mbs2 <- getData handle $ TAG2 0x9F 0x77         -- 电子现金上限
    let limit = case mbs2 of
                    Just (decode -> S2 0x9F 0x77 bs) -> bsToInt bs
                    Nothing -> 100000
    return ECash{ecashBalance=bsToInt bs1, ecashBalanceLimit=limit}

-- PBOC借贷记，第八步：卡片行为分析
cardTradeDecide :: Transfer -> Terminal -> Card -> Trade -> IO AC
cardTradeDecide handle terminal card trade = do
    S1 0x80 bs <- generateAC handle (acType trade) $ generateDOL [generateDO terminal, generateDO trade] $ cdol1 card
    return $ decodeAC bs

--------------------------------读卡操作------------------------------------
readCard handle trade = do
    Just appInfo <- selectApp handle defaultTerminal
    card <- initApp handle appInfo defaultTerminal trade
    ecash <- readECash handle
    ac <- cardTradeDecide handle defaultTerminal card trade
    return (card, ecash, ac)

