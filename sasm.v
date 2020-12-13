Require Import Bool Coq.Numbers.BinNums Coq.ZArith.BinInt.
Local Open Scope Z_scope.

Inductive Bit := false | true.
Definition bit (n : Z) : Bit :=
		match n with
		| 0 => false
		| _ => true
		end.
Coercion bit : Z >-> Bit.

Definition notbit (b1 : Bit) : Bit :=
		match b1 with
		| false => true
		| true => false
		end.
Definition orbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| false, false => false
		| _, _ => true
		end.
Definition xorbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| true, true => false
		| false, false => false
		| _, _ => true
		end.
Definition norbit (b1 b2 : Bit) : Bit := (notbit (orbit b1 b2)).
Definition xnorbit (b1 b2 : Bit) : Bit := (notbit (xorbit b1 b2)).
Definition andbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| true, true => true
		| _, _ => false
		end.
Definition xandbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| true, true => true
		| false, false => true
		| _, _ => false
		end.
Definition nandbit (b1 b2 : Bit) : Bit := notbit (andbit b1 b2).
Definition xnandbit (b1 b2 : Bit) : Bit := notbit (xandbit b1 b2).
Definition eqbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| false, false => true
		| true, true => true
		| _, _ => false
		end.


(*
 * Byte - 8 Bits
 *)

Inductive Byte : Set := byte (_ _ _ _ _ _ _ _ : Bit).
Definition zero := byte 0 0 0 0 0 0 0 0.
Definition one := byte 0 0 0 0 0 0 0 1.

Definition rshift (a : Byte) :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte 0 a1 a2 a3 a4 a5 a6 a7
		end.
Definition lshift (a : Byte) :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a2 a3 a4 a5 a6 a7 a8 0
		end.

Definition rrot (a : Byte) :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a8 a1 a2 a3 a4 a5 a6 a7
		end.
Definition lrot (a : Byte) :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a2 a3 a4 a5 a6 a7 a8 a1
		end.

Definition orbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (orbit a1 a1') (orbit a2 a2') (orbit a3 a3') (orbit a4 a4') (orbit a5 a5') (orbit a6 a6') (orbit a7 a7') (orbit a8 a8')
		end.
Definition xorbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (xorbit a1 a1') (xorbit a2 a2') (xorbit a3 a3') (xorbit a4 a4') (xorbit a5 a5') (xorbit a6 a6') (xorbit a7 a7') (xorbit a8 a8')
		end.
Definition norbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (norbit a1 a1') (norbit a2 a2') (norbit a3 a3') (norbit a4 a4') (norbit a5 a5') (norbit a6 a6') (norbit a7 a7') (norbit a8 a8')
		end.
Definition xnorbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (xnorbit a1 a1') (xnorbit a2 a2') (xnorbit a3 a3') (xnorbit a4 a4') (xnorbit a5 a5') (xnorbit a6 a6') (xnorbit a7 a7') (xnorbit a8 a8')
		end.

Definition andbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (andbit a1 a1') (andbit a2 a2') (andbit a3 a3') (andbit a4 a4') (andbit a5 a5') (andbit a6 a6') (andbit a7 a7') (andbit a8 a8')
		end.
Definition xandbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (xandbit a1 a1') (xandbit a2 a2') (xandbit a3 a3') (xandbit a4 a4') (xandbit a5 a5') (xandbit a6 a6') (xandbit a7 a7') (xandbit a8 a8')
		end.
Definition nandbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (nandbit a1 a1') (nandbit a2 a2') (nandbit a3 a3') (nandbit a4 a4') (nandbit a5 a5') (nandbit a6 a6') (nandbit a7 a7') (nandbit a8 a8')
		end.
Definition xnandbyte (b1 b2 : Byte) : Byte :=
		match b1, b2 with
			byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
				byte (xnandbit a1 a1') (xnandbit a2 a2') (xnandbit a3 a3') (xnandbit a4 a4') (xnandbit a5 a5') (xnandbit a6 a6') (xnandbit a7 a7') (xnandbit a8 a8')
		end.

Definition nat_to_byte (n : Z) : Byte :=
		byte (if (Z.geb (n mod 256) 128) then 1 else 0)
				 (if (Z.geb (n mod 128) 64) then 1 else 0)
				 (if (Z.geb (n mod 64) 32) then 1 else 0)
				 (if (Z.geb (n mod 32) 16) then 1 else 0)
				 (if (Z.geb (n mod 16) 8) then 1 else 0)
				 (if (Z.geb (n mod 8) 4) then 1 else 0)
				 (if (Z.geb (n mod 4) 2) then 1 else 0)
				 (if (Z.geb (n mod 2) 1) then 1 else 0)
.
Compute nat_to_byte 820.
Coercion nat_to_byte : Z >-> Byte.

Definition byte_to_nat (b : Byte) : Z :=
		match b with
			byte b8 b7 b6 b5 b4 b3 b2 b1 =>
				((if (eqbit b8 0) then 1 else 0) * (2 ^ 7)) +
				((if (eqbit b7 0) then 1 else 0) * (2 ^ 6)) +
				((if (eqbit b6 0) then 1 else 0) * (2 ^ 5)) +
				((if (eqbit b5 0) then 1 else 0) * (2 ^ 4)) +
				((if (eqbit b4 0) then 1 else 0) * (2 ^ 3)) +
				((if (eqbit b3 0) then 1 else 0) * (2 ^ 2)) +
				((if (eqbit b2 0) then 1 else 0) * (2 ^ 1)) +
				((if (eqbit b1 0) then 1 else 0) * (2 ^ 0))
		end.

Definition n := nat_to_byte 10.
Compute n.
Compute byte_to_nat n.


(*
 * Word - 16 Bits
 *)

Inductive Word :=
| word : Byte -> Byte -> Word.

Definition word_to_nat (w : Word) : Z :=
		match w with
		| word b1 b2 => (2^8)*byte_to_nat b1 + byte_to_nat b2
		end.
Definition nat_to_word (n : Z) : Word :=
		word (nat_to_byte (n / 2 ^ 8)) (nat_to_byte (n mod 2 ^ 8)).
Coercion nat_to_word : Z >-> Word.

Definition orword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (orbyte b1 b1') (orbyte b2 b2')
		end.
Definition xorword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (xorbyte b1 b1') (xorbyte b2 b2')
		end.
Definition norword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (norbyte b1 b1') (norbyte b2 b2')
		end.
Definition xnorword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (xnorbyte b1 b1') (xnorbyte b2 b2')
		end.

Definition andword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (andbyte b1 b1') (andbyte b2 b2')
		end.
Definition xandword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (xandbyte b1 b1') (xandbyte b2 b2')
		end.
Definition nandword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (nandbyte b1 b1') (nandbyte b2 b2')
		end.
Definition xnandword (w1 w2 : Word) : Word :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => word (xnandbyte b1 b1') (xnandbyte b2 b2')
		end.


(*
 * DWord (Double Word) - 32 Bits
 *)

Inductive DWord :=
| dword : Word -> Word -> DWord.

Definition dword_to_nat (d : DWord) : Z :=
		match d with
		| dword w1 w2 => (2^16)*word_to_nat w1 + word_to_nat w2
		end.
Definition nat_to_dword (n : Z) : DWord :=
		dword (nat_to_word (n / 2 ^ 16)) (nat_to_word (n mod 2 ^ 16)).
Coercion nat_to_dword : Z >-> DWord.

Definition ordword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (orword w1 w1') (orword w2 w2')
		end.
Definition xordword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (xorword w1 w1') (xorword w2 w2')
		end.
Definition nordword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (norword w1 w1') (norword w2 w2')
		end.
Definition xnordword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (xnorword w1 w1') (xnorword w2 w2')
		end.

Definition anddword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (andword w1 w1') (andword w2 w2')
		end.
Definition xanddword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (xandword w1 w1') (xandword w2 w2')
		end.
Definition nanddword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (nandword w1 w1') (nandword w2 w2')
		end.
Definition xnanddword (d1 d2 : DWord) : DWord :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => dword (xnandword w1 w1') (xnandword w2 w2')
		end.

Inductive ByteReg := AH | AL | BH | BL | CH | CL | DH | DL.
Inductive WordReg := AX | BX | CX | DX.
Inductive NonSPReg := EAX| EBX | ECX | EDX | ESI | EDI | EBP.
Inductive Reg := nonSPReg (r : NonSPReg) | ESP.
Inductive AnyReg := regToAnyReg (r : Reg) | EIP.


