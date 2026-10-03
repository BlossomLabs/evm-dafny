// SPDX-License-Identifier: Apache-2.0
include "util/int.dfy"

module CheckedAddition {
  import opened Int
  import U256
  import Word

  lemma Unsigned(a: u256, b: u256)
    ensures U256.Add(a,b) as int == (a as int + b as int) % TWO_256
    ensures (a > U256.Add(a,b)) <==> (a as int + b as int >= TWO_256)
    ensures a as int + b as int < TWO_256 ==> U256.Add(a,b) as int == a as int + b as int
  {
    reveal U256.Add();
    var sum := a as int + b as int;
    if sum < TWO_256 {
      assert sum % TWO_256 == sum;
    } else {
      assert TWO_256 <= sum < 2*TWO_256;
      assert sum % TWO_256 == sum-TWO_256;
    }
  }

  lemma Signed(a: i256, b: i256)
    ensures (Word.asI256(U256.Add(Word.fromI256(a),Word.fromI256(b))) as int) ==
            (if a as int + b as int < MIN_I256 then a as int + b as int + TWO_256
             else if a as int + b as int > MAX_I256 then a as int + b as int - TWO_256
             else a as int + b as int)
    ensures ((a >= 0 && Word.asI256(U256.Add(Word.fromI256(a),Word.fromI256(b))) < b) ||
             (a < 0 && Word.asI256(U256.Add(Word.fromI256(a),Word.fromI256(b))) >= b))
       <==> !(MIN_I256 <= a as int + b as int <= MAX_I256)
  {
    reveal U256.Add();
    var sum := a as int + b as int;
    if a < 0 && b < 0 {
      assert (Word.fromI256(a) as int)+(Word.fromI256(b) as int) == sum+2*TWO_256;
      if sum < MIN_I256 {
        assert (sum+2*TWO_256) % TWO_256 == sum+TWO_256;
      } else {
        assert (sum+2*TWO_256) % TWO_256 == sum+TWO_256;
      }
    } else if a < 0 || b < 0 {
      assert (Word.fromI256(a) as int)+(Word.fromI256(b) as int) == sum+TWO_256;
      if sum < 0 { assert (sum+TWO_256)%TWO_256 == sum+TWO_256; }
      else { assert (sum+TWO_256)%TWO_256 == sum; }
    } else {
      assert (Word.fromI256(a) as int)+(Word.fromI256(b) as int) == sum;
      assert sum%TWO_256 == sum;
    }
  }
}
