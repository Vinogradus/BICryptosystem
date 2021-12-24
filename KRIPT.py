import math

def ShiftNums(a, b):
    res = a
    for i in range(0, b):
        res = res << 1
        if res & 2**16:
            res += 1
        res = res & 0xFFFF
    return res


def ConcatenateNums(a, b):
    return ((a << 16) + b)

def GetPartOfBitsInBytes(block, len_, dir_ = 'left'):
    num = int.from_bytes(block, 'big') 
    if dir_ == 'left':
        mask = 0xFFFFFFFF - (2 ** (32 - len_) - 1)
        num = (num & mask) >> (32 - len_)
    elif dir_ == 'right':
        mask = (2 ** len_) - 1
        num = num & mask
    res = num.to_bytes(len_ // 8, 'big')
    return res  

def XORBytes(bytesA, bytesB):
    bytesLen = len(bytesA)
    numA = int.from_bytes(bytesA, 'big')
    numB = int.from_bytes(bytesB, 'big')
    resNum = numA ^ numB
    return resNum.to_bytes(bytesLen, 'big')

class Crypto:
    def __init__(self, instrFileName, keyFileName):
        self.n = 32
        self.byteLen = 8
        instrFile = open(instrFileName, 'r')
        sArray = instrFile.readline().rstrip('\n').split(' ')
        self.s = {}
        for i in range(0, len(sArray)):
            self.s[i] = int(sArray[i])

        self.sBlockSize = int(math.log(len(self.s), 2))
        self.p = instrFile.readline().rstrip('\n').split(' ')
        for i in range(0, len(self.p)):
            self.p[i] = int(self.p[i])

        self.order = instrFile.readline().rstrip('\n')

        self.dop = int(instrFile.readline().rstrip('\n'))

        self.roundKeyStr = instrFile.readline().rstrip('\n').split(' ')
        self.roundKeyStr = self.roundKeyStr[:-1]

        instrFile.close()

        keyFile =  open(keyFileName, 'rb')
        self.key = keyFile.read()
        self.k1 = int.from_bytes(self.key[:len(self.key)//2], 'big')
        self.k2 = int.from_bytes(self.key[len(self.key)//2:], 'big')

        keyFile.close()

        self.roundKeys = self.GetRoundKeys()

    def GetRoundKeys(self):
        round_keys = []
        
        #RK1 - (k1^25981)|(k2^9547),k1^12131
        rk1_l = (self.k1 ^ 25981) | (self.k2 ^ 9547)
        rk1_r = self.k1 ^ 12131
        round_keys.append(ConcatenateNums(rk1_l, rk1_r))

        #RKT - empty
        round_keys.append(0)

        #RK2 - (k1<5)^(k2)
        rk2 = (ShiftNums(self.k1, 5)) ^ self.k2
        round_keys.append(rk2)

        #RKT - empty
        round_keys.append(0)
        
        #RK3 - (k1)^(k2^25927)
        rk3 = self.k1 ^ (self.k2 ^ 25927)
        round_keys.append(rk3)

        #RK4 - (k1^13813)^(k2)
        rk4 = (self.k1 ^ 13813) ^ self.k2
        round_keys.append(rk4)

        #RK5 - (k1^9022)^(k2),k1^10467
        rk5_l = (self.k1 ^ 9022) ^ self.k2
        rk5_r = self.k1 ^ 10467
        round_keys.append(ConcatenateNums(rk5_l, rk5_r))

        return round_keys

    def Encrypt(self, fileEncryptName):
        encrFile = open(fileEncryptName, 'rb')
        textToEncr = encrFile.read()
        encrFile.close()
        blocks = []
        if len(textToEncr) // 4 < len(textToEncr) / 4:
            numOfBlocks = len(textToEncr) // 4 + 1
        else:
            numOfBlocks = len(textToEncr) // 4
        for i in range(0, numOfBlocks - 1):
            blocks.append(textToEncr[4*i:4*(i + 1)])
        blocks.append(textToEncr[4 * (numOfBlocks - 1):])
        if self.dop == 3:
            if len(blocks) < 2:
                print('LOLLLLL')
                return b''
            blocksToEncrBeforeCompl = len(blocks) - 2
        else:
            blocksToEncrBeforeCompl = len(blocks) - 1
        for i in range(0, blocksToEncrBeforeCompl):
            blocks[i] = self.BlockEncr(blocks[i])
        self.ComplementAndEncr(blocks, len(textToEncr))
        encrText = b''
        for block in blocks:
            encrText += block
        return encrText

    def BlockEncr(self, block):
        res = block
        for round_num in range(0, len(self.order)):
            if self.order[round_num] == 's':
                res = self.SP(round_num, res)
            elif self.order[round_num] == 'w':
                res = self.Vanish(round_num, res)
            elif self.order[round_num] == 't':
                res = self.Tau(round_num, res)
            elif self.order[round_num] == 'f':
                res = self.Feistel(round_num, res)
            elif self.order[round_num] == 'l':
                res = self.LaysMessi(round_num, res)
        return res

    def ComplementAndEncr(self, blocks, fulLen):
        if self.dop == 1:
            while(len(blocks[-1]) % (self.n // self.byteLen) != 0):
                blocks[-1] += b'\x00'
            blocks.append(fulLen.to_bytes(self.n // self.byteLen, 'big'))
            blocks[-2] = self.BlockEncr(blocks[-2])
            blocks[-1] = self.BlockEncr(blocks[-1])
        elif self.dop == 2:
            if (len(blocks[-1]) % (self.n // self.byteLen) == 0):
                blocks.append(b'\x80\x00\x00\x00')
                blocks[-2] = self.BlockEncr(blocks[-2])
                blocks[-1] = self.BlockEncr(blocks[-1])
            else:
                blocks[-1] += b'\x80'
                while(len(blocks[-1]) % (self.n // self.byteLen) != 0):
                    blocks[-1] += b'\x00'

                blocks[-1] = self.BlockEncr(blocks[-1])
        elif self.dop == 3:
            if (len(blocks[-1]) % (self.n // self.byteLen) != 0):
                lastBlockLen = len(blocks[-1]) * self.byteLen
                encrPrelastBlock = self.BlockEncr(blocks[-2])
                y_block = GetPartOfBitsInBytes(
                    encrPrelastBlock,
                    self.n - lastBlockLen,
                    dir_ = 'right')
                blocks[-2] = self.BlockEncr(blocks[-1] + y_block)
                blocks[-1] = GetPartOfBitsInBytes(
                    encrPrelastBlock,
                    lastBlockLen,
                    dir_ = 'left')
            else:
                save_block = blocks[-2]
                blocks[-2] = self.BlockEncr(blocks[-1])
                blocks[-1] = self.BlockEncr(save_block)     

    def SP(self, round_, block):
        blockLen = len(block)

        out = int.from_bytes(block, 'big') ^ self.roundKeys[round_]
        
        s_blocks = []
        numOfSBlocks = blockLen * self.byteLen // self.sBlockSize
        const = 2 ** self.sBlockSize - 1
        for i in range(0, numOfSBlocks):
            shift = (numOfSBlocks - i - 1) * self.sBlockSize
            added = (out & (const << shift)) >> shift
            s_blocks.append(added)
        
        new_s_blocks = []
        for s_block in s_blocks:
            new_s_blocks.append(self.s[s_block])
        s_blocks = new_s_blocks

        out = 0
        for s_block in s_blocks:
            out = out << self.sBlockSize
            out += s_block

        new_out = 0
        for i in range(0, blockLen * self.byteLen):
            bit = (out & (1 << i)) >> i
            new_pos = (self.p[0] * i + self.p[1]) % (blockLen * self.byteLen)
            new_out += bit << new_pos
        out = new_out
        b_out = out.to_bytes(blockLen, 'big')
        return b_out

    def Vanish(self, round_, block):
        out = (
            int.from_bytes(block, 'big') ^ self.roundKeys[round_]
            ).to_bytes(self.n // self.byteLen, 'big')
        return out

    def Tau(self, round_, block):
        out = block[len(block) // 2:] + block[:len(block) // 2]
        return out

    def Feistel(self, round_, block):
        x1 = block[:len(block) // 2]
        x2 = block[len(block) // 2:]
        spX2 = self.SP(round_, x2)
        out = x2 + XORBytes(x1, spX2)
        return out

    def LaysMessi(self, round_, block):
        x1 = block[:len(block) // 2]
        x2 = block[len(block) // 2:]
        x1XORx2 = XORBytes(x1, x2)
        spXOR = self.SP(round_, x1XORx2)
        leftPart = XORBytes(x1, spXOR)
        rightPart = XORBytes(x2, spXOR)
        out = leftPart + rightPart
        return out

def PrintEncrToFile(encrText, fileName):
    with open(fileName, 'wb') as f:
        f.write(encrText)

if __name__ == '__main__':
    crypto = Crypto('instructions.in', 'key.in')
    encrypted = crypto.Encrypt('test.in')
    PrintEncrToFile(encrypted, 'test.out')
    
