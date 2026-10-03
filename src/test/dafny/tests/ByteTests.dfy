include "../../../dafny/util/bytes.dfy"
include "../utils.dfy"

module ByteTests{
    import opened ByteUtils
    import opened Utils

    method {:test} {:isolate_assertions} ReadTests() {
        // U8
        AssertAndExpect(ReadUint8([],0) == 0);
        AssertAndExpect(ReadUint8([0],0) == 0);
        AssertAndExpect(ReadUint8([1],0) == 1);
        AssertAndExpect(ReadUint8([1],1) == 0);
        AssertAndExpect(ReadUint8([1,2],0) == 1);
        AssertAndExpect(ReadUint8([1,2],1) == 2);
        // U16
        AssertAndExpect(ReadUint16([],0) == 0);
        AssertAndExpect(ReadUint16([0],0) == 0);
        AssertAndExpect(ReadUint16([0],1) == 0);
        AssertAndExpect(ReadUint16([0,0],0) == 0);
        AssertAndExpect(ReadUint16([0,1],0) == 1);
        AssertAndExpect(ReadUint16([1,0],0) == 256);
        AssertAndExpect(ReadUint16([0xFF],0) == 0xFF00);
        AssertAndExpect(ReadUint16([0xFF,0],0) == 0xFF00);
        AssertAndExpect(ReadUint16([0xFF,1],0) == 0xFF01);
        // U32
        AssertAndExpect(ReadUint32([],0) == 0);
        AssertAndExpect(ReadUint32([0],0) == 0);
        AssertAndExpect(ReadUint32([0xFF],0) == 0xFF00_0000);
        AssertAndExpect(ReadUint32([0,0xFF],0) == 0x00FF_0000);
        AssertAndExpect(ReadUint32([0,0xFF,0],0) == 0x00FF_0000);
        AssertAndExpect(ReadUint32([0,0xFF,0,0xD],0) == 0x00FF_000D);
        AssertAndExpect(ReadUint32([0,0xFF,0,0xD],1) == 0xFF_000D00);
        // U64
        AssertAndExpect(ReadUint64([],0) == 0);
        AssertAndExpect(ReadUint64([0],0) == 0);
        AssertAndExpect(ReadUint64([0xFF],0) == 0xFF00_0000_0000_0000);
        AssertAndExpect(ReadUint64([0,0xFF],0) == 0x00FF_0000_0000_0000);
        AssertAndExpect(ReadUint64([0,0xFF,0],0) == 0x00FF_0000_0000_0000);
        AssertAndExpect(ReadUint64([0,0xFF,0,0xD],0) == 0x00FF_000D_0000_0000);
        AssertAndExpect(ReadUint64([0,0xFF,0,0xD],1) == 0xFF_000D00_0000_0000);
        AssertAndExpect(ReadUint64([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF_000D_0A0B_0000);
        AssertAndExpect(ReadUint64([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF_000D0A_0B00_0000);
        AssertAndExpect(ReadUint64([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B);
        // U128
        AssertAndExpect(ReadUint128([],0) == 0);
        AssertAndExpect(ReadUint128([0],0) == 0);
        AssertAndExpect(ReadUint128([0xFF],0) == 0xFF000000_00000000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF],0) == 0x00FF0000_00000000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF,0],0) == 0x00FF0000_00000000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF,0,0xD],0) == 0x00FF000D_00000000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF,0,0xD],1) == 0xFF000D00_00000000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF000D_0A0B0000_00000000_00000000);
        AssertAndExpect(ReadUint128([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF_000D0A_0B00_0000_00000000_00000000);
        AssertAndExpect(ReadUint128([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B_00000000_00000000);
        AssertAndExpect(ReadUint128([0xFF,0xA,0xB,0xC,0xD,0xE,0xF,0x1A,0x1B, 0x1C,0x1D,0x1E,0x1F,0x2A,0x2B,0x2C,0x2D],1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D);
        // U256
        AssertAndExpect(ReadUint256([],0) == 0);
        AssertAndExpect(ReadUint256([0],0) == 0);
        AssertAndExpect(ReadUint256([],0) == 0);
        AssertAndExpect(ReadUint256([0],0) == 0);
        AssertAndExpect(ReadUint256([0xFF],0) == 0xFF00000000000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF],0) == 0x00FF000000000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF,0],0) == 0x00FF000000000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF,0,0xD],0) == 0x00FF000D00000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF,0,0xD],1) == 0xFF000D0000000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF000D0A0B0000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF000D0A0B000000_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B_0000000000000000_0000000000000000_0000000000000000);
        AssertAndExpect(ReadUint256([0xFF,0xA,0xB,0xC,0xD,0xE,0xF,0x1A,0x1B, 0x1C,0x1D,0x1E,0x1F,0x2A,0x2B,0x2C,0x2D],1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D_0000000000000000_0000000000000000);
    }

    method {:test} {:isolate_assertions} ReadFullWordTest() {
        var bytes := [0xff] + [0xa,0xb,0xc,0xd,0xe,0xf,0x1a,0x1b] + [0x1c,0x1d,0x1e,0x1f,0x2a,0x2b,0x2c,0x2d] + [0x2e,0x2f,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f] + [0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,0x5a,0x5b];
        assert bytes[0] == 255;
        assert bytes[1] == 10;
        assert bytes[2] == 11;
        assert bytes[3] == 12;
        assert bytes[4] == 13;
        assert bytes[5] == 14;
        assert bytes[6] == 15;
        assert bytes[7] == 26;
        assert bytes[8] == 27;
        assert bytes[9] == 28;
        assert bytes[10] == 29;
        assert bytes[11] == 30;
        assert bytes[12] == 31;
        assert bytes[13] == 42;
        assert bytes[14] == 43;
        assert bytes[15] == 44;
        assert bytes[16] == 45;
        assert bytes[17] == 46;
        assert bytes[18] == 47;
        assert bytes[19] == 58;
        assert bytes[20] == 59;
        assert bytes[21] == 60;
        assert bytes[22] == 61;
        assert bytes[23] == 62;
        assert bytes[24] == 63;
        assert bytes[25] == 74;
        assert bytes[26] == 75;
        assert bytes[27] == 76;
        assert bytes[28] == 77;
        assert bytes[29] == 78;
        assert bytes[30] == 79;
        assert bytes[31] == 90;
        assert bytes[32] == 91;
        assert ReadUint8(bytes,0) == 255;
        assert ReadUint8(bytes,1) == 10;
        assert ReadUint8(bytes,2) == 11;
        assert ReadUint8(bytes,3) == 12;
        assert ReadUint8(bytes,4) == 13;
        assert ReadUint8(bytes,5) == 14;
        assert ReadUint8(bytes,6) == 15;
        assert ReadUint8(bytes,7) == 26;
        assert ReadUint8(bytes,8) == 27;
        assert ReadUint8(bytes,9) == 28;
        assert ReadUint8(bytes,10) == 29;
        assert ReadUint8(bytes,11) == 30;
        assert ReadUint8(bytes,12) == 31;
        assert ReadUint8(bytes,13) == 42;
        assert ReadUint8(bytes,14) == 43;
        assert ReadUint8(bytes,15) == 44;
        assert ReadUint8(bytes,16) == 45;
        assert ReadUint8(bytes,17) == 46;
        assert ReadUint8(bytes,18) == 47;
        assert ReadUint8(bytes,19) == 58;
        assert ReadUint8(bytes,20) == 59;
        assert ReadUint8(bytes,21) == 60;
        assert ReadUint8(bytes,22) == 61;
        assert ReadUint8(bytes,23) == 62;
        assert ReadUint8(bytes,24) == 63;
        assert ReadUint8(bytes,25) == 74;
        assert ReadUint8(bytes,26) == 75;
        assert ReadUint8(bytes,27) == 76;
        assert ReadUint8(bytes,28) == 77;
        assert ReadUint8(bytes,29) == 78;
        assert ReadUint8(bytes,30) == 79;
        assert ReadUint8(bytes,31) == 90;
        assert ReadUint8(bytes,32) == 91;
        assert ReadUint16(bytes,1) == 2571;
        assert ReadUint16(bytes,3) == 3085;
        assert ReadUint16(bytes,5) == 3599;
        assert ReadUint16(bytes,7) == 6683;
        assert ReadUint16(bytes,9) == 7197;
        assert ReadUint16(bytes,11) == 7711;
        assert ReadUint16(bytes,13) == 10795;
        assert ReadUint16(bytes,15) == 11309;
        assert ReadUint16(bytes,17) == 11823;
        assert ReadUint16(bytes,19) == 14907;
        assert ReadUint16(bytes,21) == 15421;
        assert ReadUint16(bytes,23) == 15935;
        assert ReadUint16(bytes,25) == 19019;
        assert ReadUint16(bytes,27) == 19533;
        assert ReadUint16(bytes,29) == 20047;
        assert ReadUint16(bytes,31) == 23131;
        assert ReadUint32(bytes,1) == 168496141;
        assert ReadUint32(bytes,5) == 235870747;
        assert ReadUint32(bytes,9) == 471670303;
        assert ReadUint32(bytes,13) == 707472429;
        assert ReadUint32(bytes,17) == 774847035;
        assert ReadUint32(bytes,21) == 1010646591;
        assert ReadUint32(bytes,25) == 1246448717;
        assert ReadUint32(bytes,29) == 1313823323;
        assert ReadUint64(bytes,1) == 723685415333075483;
        assert ReadUint64(bytes,9) == 2025808526586883117;
        assert ReadUint64(bytes,17) == 3327942675738213951;
        assert ReadUint64(bytes,25) == 5353456476969982555;
        assert ReadUint128(bytes,1) == 13349639646525445644842885672799513645;
        assert ReadUint128(bytes,17) == 61389706831319006209094032601855777371;
        AssertAndExpect(ReadUint256(bytes,1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D_2E2F3A3B3C3D3E3F_4A4B4C4D4E4F5A5B);
    }

    method {:test} LeftPadTests() {
        AssertAndExpect(LeftPad([0],2) == [0,0]);
        AssertAndExpect(LeftPad([1],2) == [0,1]);
        AssertAndExpect(LeftPad([1],4) == [0,0,0,1]);
        AssertAndExpect(LeftPad([1,2],4) == [0,0,1,2]);
    }
}
