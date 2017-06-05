/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Bitwise operations using binary representation of integers.
-/

import .basic

namespace pos_num

  def lor : pos_num → pos_num → pos_num
  | 1        (bit0 q) := bit1 q
  | 1        q        := q
  | (bit0 p) 1        := bit1 p
  | p        1        := p
  | (bit0 p) (bit0 q) := bit0 (lor p q)
  | (bit0 p) (bit1 q) := bit1 (lor p q)
  | (bit1 p) (bit0 q) := bit1 (lor p q)
  | (bit1 p) (bit1 q) := bit1 (lor p q)

  def land : pos_num → pos_num → num
  | 1        (bit0 q) := 0
  | 1        _        := 1
  | (bit0 p) 1        := 0
  | _        1        := 1
  | (bit0 p) (bit0 q) := num.bit0 (land p q)
  | (bit0 p) (bit1 q) := num.bit0 (land p q)
  | (bit1 p) (bit0 q) := num.bit0 (land p q)
  | (bit1 p) (bit1 q) := num.bit1 (land p q)

  def ldiff : pos_num → pos_num → num
  | 1        (bit0 q) := 1
  | 1        _        := 0
  | (bit0 p) 1        := bit0 p
  | (bit1 p) 1        := bit0 p
  | (bit0 p) (bit0 q) := num.bit0 (ldiff p q)
  | (bit0 p) (bit1 q) := num.bit0 (ldiff p q)
  | (bit1 p) (bit0 q) := num.bit1 (ldiff p q)
  | (bit1 p) (bit1 q) := num.bit0 (ldiff p q)

  def lxor : pos_num → pos_num → num
  | 1        1        := 0
  | 1        (bit0 q) := bit1 q
  | 1        (bit1 q) := bit0 q
  | (bit0 p) 1        := bit1 p
  | (bit1 p) 1        := bit0 p
  | (bit0 p) (bit0 q) := num.bit0 (lxor p q)
  | (bit0 p) (bit1 q) := num.bit1 (lxor p q)
  | (bit1 p) (bit0 q) := num.bit1 (lxor p q)
  | (bit1 p) (bit1 q) := num.bit0 (lxor p q)

  def test_bit : pos_num → nat → bool
  | 1        0     := tt
  | 1        (n+1) := ff
  | (bit0 p) 0     := ff
  | (bit0 p) (n+1) := test_bit p n
  | (bit1 p) 0     := tt
  | (bit1 p) (n+1) := test_bit p n

  def one_bits : pos_num → nat → list nat
  | 1        d := [d]
  | (bit0 p) d := one_bits p (d+1)
  | (bit1 p) d := d :: one_bits p (d+1)

  def shiftl (p : pos_num) : nat → pos_num
  | 0     := p
  | (n+1) := bit0 (shiftl n)

  def shiftr : pos_num → nat → num
  | p        0     := 1
  | 1        (n+1) := 0
  | (bit0 p) (n+1) := shiftr p n
  | (bit1 p) (n+1) := shiftr p n

end pos_num

namespace num

  def lor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := p.lor q

  def land : num → num → num
  | 0       q       := 0
  | p       0       := 0
  | (pos p) (pos q) := p.land q

  def ldiff : num → num → num
  | 0       q       := 0
  | p       0       := p
  | (pos p) (pos q) := p.ldiff q

  def lxor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := p.lxor q

  def shiftl : num → nat → num
  | 0       n := 0
  | (pos p) n := pos (p.shiftl n)

  def shiftr : num → nat → num
  | 0       n := 0
  | (pos p) n := p.shiftr n

  def test_bit : num → nat → bool
  | 0       n := ff
  | (pos p) n := p.test_bit n

  def one_bits : num → list nat
  | 0       := []
  | (pos p) := p.one_bits 0

end num

namespace int
  open nat

  def lnot : ℤ → ℤ
  | (m : ℕ) := -[1+ m]
  | -[1+ m] := m

  def lor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.ldiff n m]
  | -[1+ m] (n : ℕ) := -[1+ nat.ldiff m n]
  | -[1+ m] -[1+ n] := -[1+ nat.land m n]

  def land : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.land m n
  | (m : ℕ) -[1+ n] := -[1+ nat.ldiff m n]
  | -[1+ m] (n : ℕ) := -[1+ nat.ldiff n m]
  | -[1+ m] -[1+ n] := -[1+ nat.lor m n]

  def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.ldiff m n
  | (m : ℕ) -[1+ n] := -[1+ nat.lor m n]
  | -[1+ m] (n : ℕ) := nat.land m n
  | -[1+ m] -[1+ n] := nat.ldiff n m

  def lxor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lxor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.lxor m n]
  | -[1+ m] (n : ℕ) := -[1+ nat.lxor m n]
  | -[1+ m] -[1+ n] := nat.lxor m n

  def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.shiftl m n
  | (m : ℕ) -[1+ n] := nat.shiftr m (nat.succ n)
  | -[1+ m] (n : ℕ) := -[1+ nat.shiftl m n]
  | -[1+ m] -[1+ n] := -[1+ nat.shiftr m (nat.succ n)]

  def shiftr : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.shiftr m n
  | (m : ℕ) -[1+ n] := nat.shiftl m (nat.succ n)
  | -[1+ m] (n : ℕ) := -[1+ nat.shiftr m n]
  | -[1+ m] -[1+ n] := -[1+ nat.shiftl m (nat.succ n)]

  def test_bit : ℤ → ℕ → bool
  | (m : ℕ) n := nat.test_bit m n
  | -[1+ m] n := bnot (nat.test_bit m n)

end int
