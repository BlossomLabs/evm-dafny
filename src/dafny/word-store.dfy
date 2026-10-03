// SPDX-License-Identifier: Apache-2.0
include "util/bytes.dfy"
module WordStoreFacts {
  import opened Int
  import ByteUtils
  import U16
  import U32
  import U64
  import U128
  import U256
  lemma Store16(mem: seq<u8>, offset: nat, value: u16)
    requires offset+2 <= |mem|
    ensures ByteUtils.WriteUint16(mem,offset,value) == mem[..offset]+U16.ToBytes(value)+mem[offset+2..]
  {
    var hi := (value / (TWO_8 as u16)) as u8;
    var lo := (value % (TWO_8 as u16)) as u8;
    var result := mem[offset:=hi][offset+1:=lo];
    forall i | 0 <= i < |mem|
      ensures result[i] == (mem[..offset]+[hi,lo]+mem[offset+2..])[i]
    {}
  }
  lemma Store32(mem: seq<u8>, offset: nat, value: u32)
    requires offset+4 <= |mem|
    ensures ByteUtils.WriteUint32(mem,offset,value) == mem[..offset]+U32.ToBytes(value)+mem[offset+4..]
  {
    var hi := (value / (TWO_16 as u32)) as u16;
    var lo := (value % (TWO_16 as u32)) as u16;
    Store16(mem,offset,hi);
    var intermediate := ByteUtils.WriteUint16(mem,offset,hi);
    Store16(intermediate,offset+2,lo);
    assert intermediate[..offset+2] == mem[..offset]+U16.ToBytes(hi);
    assert intermediate[offset+4..] == mem[offset+4..];
  }
  lemma Store64(mem: seq<u8>, offset: nat, value: u64)
    requires offset+8 <= |mem|
    ensures ByteUtils.WriteUint64(mem,offset,value) == mem[..offset]+U64.ToBytes(value)+mem[offset+8..]
  {
    var hi := (value / (TWO_32 as u64)) as u32;
    var lo := (value % (TWO_32 as u64)) as u32;
    Store32(mem,offset,hi);
    var intermediate := ByteUtils.WriteUint32(mem,offset,hi);
    Store32(intermediate,offset+4,lo);
    assert intermediate[..offset+4] == mem[..offset]+U32.ToBytes(hi);
    assert intermediate[offset+8..] == mem[offset+8..];
  }
  lemma Store128(mem: seq<u8>, offset: nat, value: u128)
    requires offset+16 <= |mem|
    ensures ByteUtils.WriteUint128(mem,offset,value) == mem[..offset]+U128.ToBytes(value)+mem[offset+16..]
  {
    var hi := (value / (TWO_64 as u128)) as u64;
    var lo := (value % (TWO_64 as u128)) as u64;
    Store64(mem,offset,hi);
    var intermediate := ByteUtils.WriteUint64(mem,offset,hi);
    Store64(intermediate,offset+8,lo);
    assert intermediate[..offset+8] == mem[..offset]+U64.ToBytes(hi);
    assert intermediate[offset+16..] == mem[offset+16..];
  }
  lemma Store256(mem: seq<u8>, offset: nat, value: u256)
    requires offset+32 <= |mem|
    ensures ByteUtils.WriteUint256(mem,offset,value) == mem[..offset]+U256.ToBytes(value)+mem[offset+32..]
  {
    var hi := (value / (TWO_128 as u256)) as u128;
    var lo := (value % (TWO_128 as u256)) as u128;
    Store128(mem,offset,hi);
    var intermediate := ByteUtils.WriteUint128(mem,offset,hi);
    Store128(intermediate,offset+16,lo);
    assert intermediate[..offset+16] == mem[..offset]+U128.ToBytes(hi);
    assert intermediate[offset+32..] == mem[offset+32..];
  }
}
