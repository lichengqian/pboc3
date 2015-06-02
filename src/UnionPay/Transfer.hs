module UnionPay.Transfer where

import qualified Data.ByteString.Lazy as B

-- 底层通信函数
data Transfer = Transfer {
    transfer :: B.ByteString -> IO B.ByteString
}