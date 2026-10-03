/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
module EvmArithmetic {
  // Compute absolute value
  function Abs(x: int) : nat {
    if x >= 0 then x else -x
  }

  // =========================================================
  // Exponent
  // =========================================================

  /**
    * Compute n^k.
    */
  function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {
    if k == 0 then 1
    else if k == 1 then n
    else
      var p := k / 2;
      var np := Pow(n,p);
      if p*2 == k then np * np
      else
        np * np * n
  }

  // Simple lemma about POW.
  lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {
    if k == 0 {
      assert Pow(2,k) == 1;
    } else if k == 1 {
      assert Pow(2,k) == 2;
    } else {
      lemma_pow2(k/2);
    }
  }

  lemma ProductMonotone(a:nat,b:nat,c:nat)
    requires a <= b
    ensures a*c <= b*c
  { assert b*c == a*c+(b-a)*c; }

  lemma Quotient(a:nat,b:nat,d:nat)
    requires d > 0 && b < d
    ensures (a*d+b)/d == a
    ensures (a*d+b)%d == b
  {
    var value := a*d+b;
    var q := value/d;
    assert value == q*d+value%d;
    if q < a {
      ProductMonotone(q+1,a,d);
      assert (q+1)*d == q*d+d;
      assert value < q*d+d;
    } else if q > a {
      ProductMonotone(a+1,q,d);
      assert (a+1)*d == a*d+d;
      assert value >= q*d;
    }
  }

  lemma ModuloByteStep(n:nat,k:nat)
    requires k > 0
    ensures (n % (256*k))/256 == (n/256)%k
    ensures (n % (256*k))%256 == n%256
  {
    var q := (n/256)/k;
    var r := (n/256)%k;
    var t := n%256;
    assert n == (q*k+r)*256+t;
    assert n == q*(256*k)+(256*r+t);
    assert 256*r+t < 256*k;
    Quotient(q,256*r+t,256*k);
    Quotient(r,t,256);
  }
}
