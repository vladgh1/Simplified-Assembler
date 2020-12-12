Require Import Bool Coq.Numbers.BinNums Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Check 1000000000000000.

Inductive Bit := false | true.
Definition bit (n : Z) : Bit :=
	match n with
		| 0 => false
		| _ => true
	end.
Coercion bit : Z >-> Bit.
Compute bit 1.
Compute bit 0.
Compute bit 4.

Inductive Byte : Set := byte (_ _ _ _ _ _ _ _ : Bit).
Definition zero := byte 0 0 0 0 0 0 0 0.
Definition one := byte 0 0 0 0 0 0 0 1.

Definition app1 (f : Bit -> Bit) (a : Byte) :=
  match a with
    | byte a1 a2 a3 a4 a5 a6 a7 a8 =>
      byte (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7) (f a8)  end.

Definition app2 (f : Bit -> Bit -> Bit) (a b : Byte) :=
  match a, b with
    | byte a1 a2 a3 a4 a5 a6 a7 a8,
      byte b1 b2 b3 b4 b5 b6 b7 b8 =>
      byte (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4)
      (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8)
  end.

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

Definition andbyte (b1 b2 : Byte) : Byte :=
	match b1, b2 with
		byte a1 a2 a3 a4 a5 a6 a7 a8, byte a1' a2' a3' a4' a5' a6' a7' a8' =>
			byte (andbit a1 a1') (andbit a2 a2') (andbit a3 a3') (andbit a4 a4') (andbit a5 a5') (andbit a6 a6') (andbit a7 a7') (andbit a8 a8')
	end.

Compute (192/10) mod 10.
Compute 199 mod 2^8.
Compute bit (if (Z.geb (7 mod 4) 2) then 1 else 0).
Compute byte 1 1 1 1 1 1 1 1.
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
 * Word - 8 Bits
 *)

Inductive Word :=
| word (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ : Bit)
| bword : Byte -> Byte -> Word.

Definition x := (bword (byte 0 0 0 0 0 0 0 0) (byte 0 0 0 1 0 0 1 0)).
Definition y := (word 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1 0).
Compute x.
Compute y.
Definition word_to_bword (w : Word) : Word :=
		match w with
		| word b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 =>
			bword (byte b1 b2 b3 b4 b5 b6 b7 b8) (byte b9 b10 b11 b12 b13 b14 b15 b16)
		| bword b1 b2 => bword b1 b2
		end.
Definition bword_to_word (w : Word) : Word :=
		match w with
		| word b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 =>
			word b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
		| bword b1 b2 => 
			match b1, b2 with
				byte b11 b12 b13 b14 b15 b16 b17 b18,
				byte b21 b22 b23 b24 b25 b26 b27 b28 =>
				word b11 b12 b13 b14 b15 b16 b17 b18 b21 b22 b23 b24 b25 b26 b27 b28
			end
		end.
Compute word_to_bword y.
Compute bword_to_word x.

Definition word_to_nat (w : Word) : Z :=
		match w with
		| word b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 => 
			256 * (byte_to_nat (byte b1 b2 b3 b4 b5 b6 b7 b8)) + (byte_to_nat (byte b9 b10 b11 b12 b13 b14 b15 b16))
		| bword b1 b2 => 256*byte_to_nat b1 + byte_to_nat b2
		end.
Definition nat_to_word (n : Z) : Word :=
		bword (nat_to_byte (n / 2 ^ 8)) (nat_to_byte (n mod 2 ^ 8)).



(*
 * DWord (Double Word) - 16 Bits
 *)


Inductive DWord :=
| dword (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ : Bit)
| bdword : Word -> Word -> DWord.
Definition dword_to_nat (d : DWord) : Z :=
		match d with
		| dword b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
				   b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 => 
			65536*(word_to_nat (word b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16)) +
			(word_to_nat (word b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32))
		| bdword w1 w2 => 65536*word_to_nat w1 + word_to_nat w2
		end.

Compute nat_to_word (17 / 2 ^ 16).
Definition nat_to_dword (n : Z) : DWord :=
		bdword (nat_to_word (n / 2 ^ 16)) (nat_to_word (n mod 2 ^ 16)).


Inductive ByteReg := AH | AL | BH | BL | CH | CL | DH | DL.
Inductive WordReg := AX | BX | CX | DX.
Inductive NonSPReg := EAX| EBX | ECX | EDX | ESI | EDI | EBP.
Inductive Reg := nonSPReg (r : NonSPReg) | ESP.
Inductive AnyReg := regToAnyReg (r : Reg) | EIP.


