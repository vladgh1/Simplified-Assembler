Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.
Open Scope list_scope.

Section SASM.
Inductive Bit := bfalse | btrue.
Scheme Equality for Bit.
Definition bit (n : Z) : Bit :=
		match n with
		| 0 => bfalse
		| _ => btrue
		end.
Coercion bit : Z >-> Bit.

Definition bit_to_nat (b : Bit) : Z :=
		match b with
		| bfalse => 0
		| btrue => 1
		end.

Definition notbit (b1 : Bit) : Bit :=
		match b1 with
		| bfalse => btrue
		| btrue => bfalse
		end.
Definition orbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| bfalse, bfalse => bfalse
		| _, _ => btrue
		end.
Definition xorbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| btrue, btrue => bfalse
		| bfalse, bfalse => bfalse
		| _, _ => btrue
		end.
Definition norbit (b1 b2 : Bit) : Bit := (notbit (orbit b1 b2)).
Definition xnorbit (b1 b2 : Bit) : Bit := (notbit (xorbit b1 b2)).
Definition andbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| btrue, btrue => btrue
		| _, _ => bfalse
		end.
Definition xandbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| btrue, btrue => btrue
		| bfalse, bfalse => btrue
		| _, _ => bfalse
		end.
Definition nandbit (b1 b2 : Bit) : Bit := notbit (andbit b1 b2).
Definition xnandbit (b1 b2 : Bit) : Bit := notbit (xandbit b1 b2).
Definition eqbit (b1 b2 : Bit) : Bit :=
		match b1, b2 with
		| bfalse, bfalse => btrue
		| btrue, btrue => btrue
		| _, _ => bfalse
		end.

Definition paritybit (b : Bit) : Z :=
		match b with
		| bfalse => 0
		| btrue => 1
		end.

(*
 * Byte - 8 Bits
 *)

Inductive Byte : Set := byte (_ _ _ _ _ _ _ _ : Bit).
Definition zero := byte 0 0 0 0 0 0 0 0.
Definition one := byte 0 0 0 0 0 0 0 1.
Scheme Equality for Byte.

(* Byte Shift Operations *)
Definition rshiftbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte 0 a1 a2 a3 a4 a5 a6 a7
		end.
Definition lshiftbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a2 a3 a4 a5 a6 a7 a8 0
		end.

Definition rashiftbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a1 0 a2 a3 a4 a5 a6 a7
		end.
Definition lashiftbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a1 a3 a4 a5 a6 a7 a8 0
		end.

Definition rrotbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a8 a1 a2 a3 a4 a5 a6 a7
		end.
Definition lrotbyte (a : Byte) : Byte :=
		match a with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 => byte a2 a3 a4 a5 a6 a7 a8 a1
		end.

(* Byte Not Operation *)
Definition notbyte (b : Byte) : Byte :=
		match b with
		| byte a1 a2 a3 a4 a5 a6 a7 a8 =>
		byte (notbit a1) (notbit a2) (notbit a3) (notbit a4)
				 (notbit a5) (notbit a6) (notbit a7) (notbit a8)
		end.

(* Byte Or Operations *)
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

(* Byte And Operations *)
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

Definition paritybyte (b : Byte) : Z :=
		match b with
		| byte b1 b2 b3 b4 b5 b6 b7 b8 =>
			if (Z.eqb ((bit_to_nat b1) + (bit_to_nat b2) + (bit_to_nat b3) + (bit_to_nat b4) + (bit_to_nat b5) + (bit_to_nat b6) + (bit_to_nat b7) + (bit_to_nat b8)) 0)
			then 1
			else if (Z.eqb ((bit_to_nat b1) + (bit_to_nat b2) + (bit_to_nat b3) + (bit_to_nat b4) + (bit_to_nat b5) + (bit_to_nat b6) + (bit_to_nat b7) + (bit_to_nat b8)) 2)
			then 1
			else if (Z.eqb ((bit_to_nat b1) + (bit_to_nat b2) + (bit_to_nat b3) + (bit_to_nat b4) + (bit_to_nat b5) + (bit_to_nat b6) + (bit_to_nat b7) + (bit_to_nat b8)) 4)
			then 1
			else if (Z.eqb ((bit_to_nat b1) + (bit_to_nat b2) + (bit_to_nat b3) + (bit_to_nat b4) + (bit_to_nat b5) + (bit_to_nat b6) + (bit_to_nat b7) + (bit_to_nat b8)) 6)
			then 1
			else if (Z.eqb ((bit_to_nat b1) + (bit_to_nat b2) + (bit_to_nat b3) + (bit_to_nat b4) + (bit_to_nat b5) + (bit_to_nat b6) + (bit_to_nat b7) + (bit_to_nat b8)) 8)
			then 1
			else 0
		end.
		  

Definition signbyte (b : Byte) : Z :=
		match b with
		| byte b1 _ _ _ _ _ _ _ => bit_to_nat b1
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

Definition acmpbyte (b1 b2 : Byte) : Z :=
		match b1, b2 with
		| byte btrue a2 a3 a4 a5 a6 a7 a8,
		  byte bfalse a2' a3' a4' a5' a6' a7' a8' => -1
		
		| byte bfalse a2 a3 a4 a5 a6 a7 a8,
		  byte btrue a2' a3' a4' a5' a6' a7' a8' => 1
		
		| byte bfalse a2 a3 a4 a5 a6 a7 a8,
		  byte bfalse a2' a3' a4' a5' a6' a7' a8' => if (Z.gtb (byte_to_nat b1) (byte_to_nat b2)) then 1 else if (Z.eqb (byte_to_nat b1) (byte_to_nat b2)) then 0 else -1
		
		| byte btrue a2 a3 a4 a5 a6 a7 a8,
		  byte btrue a2' a3' a4' a5' a6' a7' a8' => if (Z.gtb (byte_to_nat b1) (byte_to_nat b2)) then -1 else if (Z.eqb (byte_to_nat b1) (byte_to_nat b2)) then 0 else 1
		end.

Definition sumbyte (b1 b2 : Byte) : Byte :=
		nat_to_byte (byte_to_nat b1 + byte_to_nat b2).
Definition difbyte (b1 b2 : Byte) : Byte :=
		nat_to_byte (byte_to_nat b1 - byte_to_nat b2).
Definition mulbyte (b1 b2 : Byte) : Byte :=
		nat_to_byte (byte_to_nat b1 * byte_to_nat b2).
Definition divbyte (b1 b2 : Byte) : Byte :=
		nat_to_byte (byte_to_nat b1 / byte_to_nat b2).

Compute sumbyte (nat_to_byte 5) (nat_to_byte 5).
Compute sumbyte (nat_to_byte 0xFF) (nat_to_byte 1).
Compute difbyte 10 5.
Compute mulbyte 10 2.
Compute divbyte 10 2.

(*
 * Word - 16 Bits
 *)

Inductive Word :=
| word : Byte -> Byte -> Word.
Scheme Equality for Word.

Definition word_to_nat (w : Word) : Z :=
		match w with
		| word b1 b2 => (2^8)*byte_to_nat b1 + byte_to_nat b2
		end.
Definition nat_to_word (n : Z) : Word :=
		word (nat_to_byte (n / 2 ^ 8)) (nat_to_byte (n mod 2 ^ 8)).
Coercion nat_to_word : Z >-> Word.

(* Word Not Operation *)
Definition notword (a : Word) : Word :=
		match a with
		| word a1 a2 => word (notbyte a1) (notbyte a2)
		end.

(* Word Shift Operations *)
Definition rshiftword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte 0 a1 a2 a3 a4 a5 a6 a7) (byte a8 a9 a10 a11 a12 a13 a14 a15)
		end.
Definition lshiftword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte a2 a3 a4 a5 a6 a7 a8 a9) (byte a10 a11 a12 a13 a14 a15 a16 0)
		end.

Definition rashiftword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte a1 0 a2 a3 a4 a5 a6 a7) (byte a8 a9 a10 a11 a12 a13 a14 a15)
		end.
Definition lashiftword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte a1 a3 a4 a5 a6 a7 a8 a9) (byte a10 a11 a12 a13 a14 a15 a16 0)
		end.

Definition rrotword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte a16 a1 a2 a3 a4 a5 a6 a7) (byte a8 a9 a10 a11 a12 a13 a14 a15)
		end.
Definition lrotword (a : Word) : Word :=
		match a with
		| word (byte a1 a2 a3 a4 a5 a6 a7 a8) (byte a9 a10 a11 a12 a13 a14 a15 a16)
			=> word (byte a2 a3 a4 a5 a6 a7 a8 a9) (byte a10 a11 a12 a13 a14 a15 a16 a1)
		end.

(* Word Or Operations *)
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

(* Word And Operations *)
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

Definition parityword (w : Word) : Z :=
		match w with
		| word b1 b2 => if (Z.eqb ((paritybyte b1) + (paritybyte b2)) 0) then 1
										else if (Z.eqb ((paritybyte b1) + (paritybyte b2)) 2) then 1
										else 0
		end.
Compute parityword (nat_to_word 10).

Definition signword (w : Word) : Z :=
		match w with
		| word b1 b2 => signbyte b1
		end.
Compute signword (nat_to_word 0xF000).


Definition acmpword (w1 w2 : Word) : Z :=
		match w1, w2 with
		| word b1 b2, word b1' b2' => if (Z.eqb (acmpbyte b1 b1') 0)
																	then (acmpbyte b2 b2')
																	else (acmpbyte b1 b1')
		end.
Compute (nat_to_word 0xCFFF).
Compute acmpword (nat_to_word 0xCFFF) (0xEFFF).

Compute nat_to_word 0xFF.
Compute word_to_nat 0xFF.
Definition sumword (w1 w2 : Word) : Word :=
		nat_to_word (word_to_nat w1 + word_to_nat w2).
Definition difword (w1 w2 : Word) : Word :=
		nat_to_word (word_to_nat w1 - word_to_nat w2).
Definition mulword (w1 w2 : Word) : Word :=
		nat_to_word (word_to_nat w1 * word_to_nat w2).
Definition divword (w1 w2 : Word) : Word :=
		nat_to_word (word_to_nat w1 / word_to_nat w2).
Compute sumword 5 5.
Compute difword 5 6.
Compute mulword 5 2.
Compute divword 10 5.

(*
 * DWord (Double Word) - 32 Bits
 *)

Inductive DWord :=
| dword : Word -> Word -> DWord.
Scheme Equality for DWord.

Definition dword_to_nat (d : DWord) : Z :=
		match d with
		| dword w1 w2 => (2^16)*word_to_nat w1 + word_to_nat w2
		end.
Definition nat_to_dword (n : Z) : DWord :=
		dword (nat_to_word (n / 2 ^ 16)) (nat_to_word (n mod 2 ^ 16)).
Coercion nat_to_dword : Z >-> DWord.

(* Double Word Not Operation *)
Definition dwordword (a : DWord) : DWord :=
		match a with
		| dword a1 a2 => dword (notword a1) (notword a2)
		end.

(* Double Word Shift operations *)
Definition rshiftdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
									(byte a9 a10 a11 a12 a13 a14 a15 a16))
						(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
									(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte 0 a1 a2 a3 a4 a5 a6 a7)
										 (byte a8 a9 a10 a11 a12 a13 a14 a15))
							 (word (byte a16 a17 a18 a19 a20 a21 a22 a23)
										 (byte a24 a25 a26 a27 a28 a29 a30 a31))
		end.
Definition lshiftdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
						(byte a9 a10 a11 a12 a13 a14 a15 a16))
			(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
						(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte a2 a3 a4 a5 a6 a7 a8 a9)
									 	 (byte a10 a11 a12 a13 a14 a15 a16 a17))
							 (word (byte a18 a19 a20 a21 a22 a23 a24 a15)
										 (byte a26 a27 a28 a29 a30 a31 a32 0))
		end.

Definition rashiftdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
									(byte a9 a10 a11 a12 a13 a14 a15 a16))
						(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
									(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte a1 0 a2 a3 a4 a5 a6 a7)
										 (byte a8 a9 a10 a11 a12 a13 a14 a15))
							 (word (byte a16 a17 a18 a19 a20 a21 a22 a23)
										 (byte a24 a25 a26 a27 a28 a29 a30 a31))
		end.
Definition lashiftdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
						(byte a9 a10 a11 a12 a13 a14 a15 a16))
			(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
						(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte a1 a3 a4 a5 a6 a7 a8 a9)
									 	 (byte a10 a11 a12 a13 a14 a15 a16 a17))
							 (word (byte a18 a19 a20 a21 a22 a23 a24 a15)
										 (byte a26 a27 a28 a29 a30 a31 a32 0))
		end.

Definition rrotdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
									(byte a9 a10 a11 a12 a13 a14 a15 a16))
						(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
									(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte a32 a1 a2 a3 a4 a5 a6 a7)
										(byte a8 a9 a10 a11 a12 a13 a14 a15))
							(word (byte a16 a17 a18 a19 a20 a21 a22 a23)
										(byte a24 a25 a26 a27 a28 a29 a30 a31))
		end.
Definition lrotdword (a : DWord) : DWord :=
		match a with
		| dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
									(byte a9 a10 a11 a12 a13 a14 a15 a16))
						(word (byte a17 a18 a19 a20 a21 a22 a23 a24)
									(byte a25 a26 a27 a28 a29 a30 a31 a32))
			=> dword (word (byte a2 a3 a4 a5 a6 a7 a8 a9)
										 (byte a10 a11 a12 a13 a14 a15 a16 a17))
							 (word (byte a18 a19 a20 a21 a22 a23 a24 a15)
										 (byte a26 a27 a28 a29 a30 a31 a32 a1))
		end.

(* Double Word Not Operation *)
Definition notdword (d : DWord) : DWord :=
		match d with
		| dword w1 w2 => dword (notword w1) (notword w2)
		end.

(* Double Word Or Operations *)
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

(* Double Word And Operations *)
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

Definition paritydword (d : DWord) : Z :=
		match d with
		| dword w1 w2 => if (Z.eqb ((parityword w1) + (parityword w2)) 0) then 1
										else if (Z.eqb ((parityword w1) + (parityword w2)) 2) then 1
										else 0
		end.
Compute paritydword (nat_to_dword 10).

Definition signdword (d : DWord) : Z :=
		match d with
		| dword w1 w2 => signword w1
		end.
Compute signdword (nat_to_dword 0xF0000000).

Definition acmpdword (d1 d2 : DWord) : Z :=
		match d1, d2 with
		| dword w1 w2, dword w1' w2' => if (Z.eqb (acmpword w1 w1') 0)
																		then (acmpword w2 w2')
																		else (acmpword w1 w1')
		end.
Compute acmpdword (nat_to_dword 10) (nat_to_dword 9).

Definition sumdword (d1 d2 : DWord) : DWord :=
		nat_to_dword (dword_to_nat d1 + dword_to_nat d2).
Definition difdword (d1 d2 : DWord) : DWord :=
		nat_to_dword (dword_to_nat d1 - dword_to_nat d2).
Definition muldword (d1 d2 : DWord) : DWord :=
		nat_to_dword (dword_to_nat d1 * dword_to_nat d2).
Definition divdword (d1 d2 : DWord) : DWord :=
		nat_to_dword (dword_to_nat d1 / dword_to_nat d2).

(*
 * QWord (Quad Word) - 64 Bits
 *)

Inductive QWord :=
| qword : DWord -> DWord -> QWord.
Scheme Equality for QWord.

Definition qword_to_nat (d : QWord) : Z :=
		match d with
		| qword d1 d2 => (2^32)*dword_to_nat d1 + dword_to_nat d2
		end.
Definition nat_to_qword (n : Z) : QWord :=
		qword (nat_to_dword (n / 2 ^ 32)) (nat_to_dword (n mod 2 ^ 32)).
Coercion nat_to_qword : Z >-> QWord.

(* Quad Word Shift operations *)
Definition rshiftqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte 0 a1 a2 a3 a4 a5 a6 a7)
														(byte a8 a9 a10 a11 a12 a13 a14 a15))
											(word (byte a16 a17 a18 a19 a20 a21 a22 a23)
														(byte a24 a25 a26 a27 a28 a29 a30 a31)))
							 (dword (word (byte a32 a33 a34 a35 a36 a37 a38 a39)
														(byte a40 a41 a42 a43 a44 a45 a46 a47))
											(word (byte a48 a49 a50 a51 a52 a53 a54 a55)
														(byte a56 a57 a58 a59 a60 a61 a62 a63)))
		end.
Definition lshiftqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte a2 a3 a4 a5 a6 a7 a8 a9)
														(byte a10 a11 a12 a13 a14 a15 a16 a17))
											(word (byte a18 a19 a20 a21 a22 a23 a24 a25)
														(byte a26 a27 a28 a29 a30 a31 a32 a33)))
							 (dword (word (byte a34 a35 a36 a37 a38 a39 a40 a41)
														(byte a42 a43 a44 a45 a46 a47 a48 a49))
											(word (byte a50 a51 a52 a53 a54 a55 a56 a57)
														(byte a58 a59 a60 a61 a62 a63 a64 0)))
		end.

Definition rashiftqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte a1 0 a2 a3 a4 a5 a6 a7)
														(byte a8 a9 a10 a11 a12 a13 a14 a15))
											(word (byte a16 a17 a18 a19 a20 a21 a22 a23)
														(byte a24 a25 a26 a27 a28 a29 a30 a31)))
							 (dword (word (byte a32 a33 a34 a35 a36 a37 a38 a39)
														(byte a40 a41 a42 a43 a44 a45 a46 a47))
											(word (byte a48 a49 a50 a51 a52 a53 a54 a55)
														(byte a56 a57 a58 a59 a60 a61 a62 a63)))
		end.
Definition lashiftqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte a1 a3 a4 a5 a6 a7 a8 a9)
														(byte a10 a11 a12 a13 a14 a15 a16 a17))
											(word (byte a18 a19 a20 a21 a22 a23 a24 a25)
														(byte a26 a27 a28 a29 a30 a31 a32 a33)))
							 (dword (word (byte a34 a35 a36 a37 a38 a39 a40 a41)
														(byte a42 a43 a44 a45 a46 a47 a48 a49))
											(word (byte a50 a51 a52 a53 a54 a55 a56 a57)
														(byte a58 a59 a60 a61 a62 a63 a64 0)))
		end.

Definition rrotqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte a64 a1 a2 a3 a4 a5 a6 a7)
														(byte a8 a9 a10 a11 a12 a13 a14 a15))
											(word (byte a16 a17 a18 a19 a20 a21 a22 a23)
														(byte a24 a25 a26 a27 a28 a29 a30 a31)))
							 (dword (word (byte a32 a33 a34 a35 a36 a37 a38 a39)
														(byte a40 a41 a42 a43 a44 a45 a46 a47))
											(word (byte a48 a49 a50 a51 a52 a53 a54 a55)
														(byte a56 a57 a58 a59 a60 a61 a62 a63)))
		end.
Definition lrotqword (a : QWord) : QWord :=
		match a with
		| qword (dword (word (byte a1 a2 a3 a4 a5 a6 a7 a8)
												 (byte a9 a10 a11 a12 a13 a14 a15 a16))
									 (word (byte a17 a18 a19 a20 a21 a22 a23 a24)
												 (byte a25 a26 a27 a28 a29 a30 a31 a32)))
						(dword (word (byte a33 a34 a35 a36 a37 a38 a39 a40)
												 (byte a41 a42 a43 a44 a45 a46 a47 a48))
									 (word (byte a49 a50 a51 a52 a53 a54 a55 a56)
												 (byte a57 a58 a59 a60 a61 a62 a63 a64)))
			=> qword (dword (word (byte a2 a3 a4 a5 a6 a7 a8 a9)
														(byte a10 a11 a12 a13 a14 a15 a16 a17))
											(word (byte a18 a19 a20 a21 a22 a23 a24 a25)
														(byte a26 a27 a28 a29 a30 a31 a32 a33)))
							 (dword (word (byte a34 a35 a36 a37 a38 a39 a40 a41)
														(byte a42 a43 a44 a45 a46 a47 a48 a49))
											(word	(byte a50 a51 a52 a53 a54 a55 a56 a57)
														(byte a58 a59 a60 a61 a62 a63 a64 a1)))
		end.

(* Double Word Not Operation *)
Definition notqword (q : QWord) : QWord :=
		match q with
		| qword d1 d2 => qword (notdword d1) (notdword d2)
		end.

(* Quad Word Or Operations *)
Definition orqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (ordword d1 d1') (ordword d2 d2')
		end.
Definition xorqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (xordword d1 d1') (xordword d2 d2')
		end.
Definition norqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (nordword d1 d1') (nordword d2 d2')
		end.
Definition xnorqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (xnordword d1 d1') (xnordword d2 d2')
		end.

(* Quad Word And Operations *)
Definition andqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (anddword d1 d1') (anddword d2 d2')
		end.
Definition xandqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (xanddword d1 d1') (xanddword d2 d2')
		end.
Definition nandqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (nanddword d1 d1') (nanddword d2 d2')
		end.
Definition xnandqword (q1 q2 : QWord) : QWord :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => qword (xnanddword d1 d1') (xnanddword d2 d2')
		end.

Definition parityqword (q : QWord) : Z :=
		match q with
		| qword d1 d2 => if (Z.eqb ((paritydword d1) + (paritydword d2)) 0) then 1
										else if (Z.eqb ((paritydword d1) + (paritydword d2)) 2) then 1
										else 0
		end.
Compute parityqword (nat_to_qword 10).

Definition signqword (q : QWord) : Z :=
		match q with
		| qword d1 d2 => signdword d1
		end.

Definition acmpqword (q1 q2 : QWord) : Z :=
		match q1, q2 with
		| qword d1 d2, qword d1' d2' => if (Z.eqb (acmpdword d1 d1') 0)
																		then (acmpdword d2 d2')
																		else (acmpdword d1 d1')
		end.

Definition sumqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 + qword_to_nat q2).
Definition difqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 - qword_to_nat q2).
Definition mulqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 * qword_to_nat q2).
Definition divqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 / qword_to_nat q2).

(*
 * FLAGS
 *)

Inductive CFLAGS :=
| EF (* Equal Flag *)
| GF (* Greater Flag *)
| BF (* Below Flag *)
.
Inductive EFLAGS :=
| CF (* Carry flag *)
| PF (* Parity flag: 1 if even numbers of 1 *)
| AF (* Auxiliary Carry flag *)
| ZF (* Zero flag *)
| SF (* Sign flag *)
| OF (* Overflow flag *)
.


(*
 * REGISTERS
 *)

Inductive ByteReg := AH | AL | BH | BL | CH | CL | DH | DL.
Inductive WordReg := AX | BX | CX | DX | SI | DI | BP.
Inductive DWordReg := EAX | EBX | ECX | EDX | ESI | EDI | EBP.
Inductive Reg := byteReg (r : ByteReg) | wordReg (r : WordReg) | dwordReg (r : DWordReg) | ESP | SP | EIP.

Coercion byteReg : ByteReg >-> Reg.
Coercion wordReg : WordReg >-> Reg.
Coercion dwordReg : DWordReg >-> Reg.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

(* Stack *)

Definition Stack := list Byte.
Definition stack0 : Stack := nil.
Compute stack0.

(* Push *)
Definition push_byte (s : Stack)(b : Byte) : Stack :=
		match b with
		| _ => (b :: s)
		end.
Definition push_word (s : Stack)(w : Word) : Stack :=
		match w with
		| word b1 b2 => push_byte (push_byte s b1) b2
		end.
Definition push_dword (s : Stack)(d : DWord) : Stack :=
		match d with
		| dword w1 w2 => push_word (push_word s w1) w2
		end.
Definition push_qword (s : Stack)(q : QWord) : Stack :=
		match q with
		| qword d1 d2 => push_dword (push_dword s d1) d2
		end.
Compute push_word stack0 (nat_to_word 10).

(* Pop *)
Definition pop_byte (s : Stack) : Stack :=
		match s with
		| nil => nil
		| _ :: s => s
		end.
Definition pop_word (s : Stack) : Stack :=
		match s with
		| nil => nil
		| _ :: nil => nil
		| _ :: _ :: s => s
		end.
Definition pop_dword (s : Stack) : Stack :=
		match s with
		| nil => nil
		| _ :: nil => nil
		| _ :: _ :: nil => nil
		| _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: s => s
		end.
Definition pop_qword (s : Stack) : Stack :=
		match s with
		| nil => nil
		| _ :: nil => nil
		| _ :: _ :: nil => nil
		| _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: _ :: _ :: _ :: nil => nil
		| _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: s => s
		end.

(* Top *)
Definition top_byte (s : Stack) : Byte :=
		match s with
		| nil => 0
		| b :: s => b
		end.
Compute top_byte (push_word nil (nat_to_word 10)).
Definition top_word (s : Stack) : Word :=
		match s with
		| nil => 0
		| b :: nil => word b 0
		| b2 :: b1 :: s => word b1 b2
		end.
Definition top_dword (s : Stack) : DWord :=
		match s with
		| nil => 0
		| b :: nil => dword (word b 0) (word 0 0)
		| b2 :: b1 :: nil => dword (word b1 b2) (word 0 0)
		| b3 :: b2 :: b1 :: nil => dword (word b1 b2) (word b3 0)
		| b4 :: b3 :: b2 :: b1 :: s => dword (word b1 b2) (word b3 b4)
		end.
Definition top_qword (s : Stack) : QWord :=
		match s with
		| nil => 0
		| b :: nil => qword (dword (word b 0) (word 0 0))
										    (dword (word 0 0) (word 0 0))
		| b2 :: b1 :: nil => qword (dword (word b1 b2) (word 0 0))
															 (dword (word 0 0) (word 0 0))
		| b3 :: b2 :: b1 :: nil => qword (dword (word b1 b2) (word b3 0))
																		 (dword (word 0 0) (word 0 0))
		| b4 :: b3 :: b2 :: b1 :: nil => qword (dword (word b1 b2) (word b3 b4))
																					 (dword (word 0 0) (word 0 0))
		| b5 :: b4 :: b3 :: b2 :: b1 :: nil => qword (dword (word b1 b2) (word b3 b4))
																								 (dword (word b5 0) (word 0 0))
		| b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: nil => qword (dword (word b1 b2) (word b3 b4))
																											 (dword (word b5 b6) (word 0 0))
		| b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: nil => qword (dword (word b1 b2) (word b3 b4))
																															(dword (word b5 b6) (word b7 0))
		| b8 :: b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: s => qword (dword (word b1 b2) (word b3 b4))
																																 (dword (word b5 b6) (word b7 b8))
		end.


(* Vars and Vals *)

Inductive Var :=
| vnull
| reg : Reg -> Var
| str : string -> Var.
Coercion reg : Reg >-> Var.
Coercion str : string >-> Var.
Scheme Equality for Var.

Inductive Val :=
| null
| bitval : Bit -> Val
| byteval : Byte -> Val
| wordval : Word -> Val
| dwordval : DWord -> Val
| qwordval : QWord -> Val.
Scheme Equality for Val.

Notation "'bit' 'ptr' A" := (bitval A)(at level 2, A at level 1).
Notation "'byte' 'ptr' A" := (byteval A)(at level 2, A at level 1).
Notation "'word' 'ptr' A" := (wordval A)(at level 2, A at level 1).
Notation "'dword' 'ptr' A" := (dwordval A)(at level 2, A at level 1).

(* Val Shift Operations *)
Definition lshiftval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval 0
		| byteval b => byteval (lshiftbyte b)
		| wordval w => wordval (lshiftword w)
		| dwordval d => dwordval (lshiftdword d)
		| qwordval q => qwordval (lshiftqword q)
		end.
Definition rshiftval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval 0
		| byteval b => byteval (rshiftbyte b)
		| wordval w => wordval (rshiftword w)
		| dwordval d => dwordval (rshiftdword d)
		| qwordval q => qwordval (rshiftqword q)
		end.
Definition lashiftval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval 0
		| byteval b => byteval (lashiftbyte b)
		| wordval w => wordval (lashiftword w)
		| dwordval d => dwordval (lashiftdword d)
		| qwordval q => qwordval (lashiftqword q)
		end.
Definition rashiftval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval 0
		| byteval b => byteval (rashiftbyte b)
		| wordval w => wordval (rashiftword w)
		| dwordval d => dwordval (rashiftdword d)
		| qwordval q => qwordval (rashiftqword q)
		end.
Definition lrotval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval b
		| byteval b => byteval (lrotbyte b)
		| wordval w => wordval (lrotword w)
		| dwordval d => dwordval (lrotdword d)
		| qwordval q => qwordval (lrotqword q)
		end.
Definition rrotval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval b
		| byteval b => byteval (rrotbyte b)
		| wordval w => wordval (rrotword w)
		| dwordval d => dwordval (rrotdword d)
		| qwordval q => qwordval (rrotqword q)
		end.

(* Val Not Operation *)
Definition notval (v : Val) : Val :=
		match v with
		| null => null
		| bitval b => bitval (notbit b)
		| byteval b => byteval (notbyte b)
		| wordval w => wordval (notword w)
		| dwordval d => dwordval (notdword d)
		| qwordval q => qwordval (notqword q)
		end.

(* Val And Operations *)
Definition andval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (andbit b1 b2)
		| byteval b1, byteval b2 => byteval (andbyte b1 b2)
		| wordval w1, wordval w2 => wordval (andword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (anddword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (andqword q1 q2)
		| a, _ => a
		end.
Definition nandval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (nandbit b1 b2)
		| byteval b1, byteval b2 => byteval (nandbyte b1 b2)
		| wordval w1, wordval w2 => wordval (nandword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (nanddword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (nandqword q1 q2)
		| a, _ => a
		end.
Definition xandval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (xandbit b1 b2)
		| byteval b1, byteval b2 => byteval (xandbyte b1 b2)
		| wordval w1, wordval w2 => wordval (xandword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (xanddword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (xandqword q1 q2)
		| a, _ => a
		end.
Definition xnandval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (xnandbit b1 b2)
		| byteval b1, byteval b2 => byteval (xnandbyte b1 b2)
		| wordval w1, wordval w2 => wordval (xnandword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (xnanddword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (xnandqword q1 q2)
		| a, _ => a
		end.

(* Val Or Operations *)
Definition orval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (orbit b1 b2)
		| byteval b1, byteval b2 => byteval (orbyte b1 b2)
		| wordval w1, wordval w2 => wordval (orword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (ordword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (orqword q1 q2)
		| a, _ => a
		end.
Definition norval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (norbit b1 b2)
		| byteval b1, byteval b2 => byteval (norbyte b1 b2)
		| wordval w1, wordval w2 => wordval (norword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (nordword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (norqword q1 q2)
		| a, _ => a
		end.
Definition xorval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (xorbit b1 b2)
		| byteval b1, byteval b2 => byteval (xorbyte b1 b2)
		| wordval w1, wordval w2 => wordval (xorword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (xordword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (xorqword q1 q2)
		| a, _ => a
		end.
Definition xnorval (v1 : Val)(v2 : Val) : Val :=
		match v1, v2 with
		| null, null => null
		| bitval b1, bitval b2 => bitval (xnorbit b1 b2)
		| byteval b1, byteval b2 => byteval (xnorbyte b1 b2)
		| wordval w1, wordval w2 => wordval (xnorword w1 w2)
		| dwordval d1, dwordval d2 => dwordval (xnordword d1 d2)
		| qwordval q1, qwordval q2 => qwordval (xnorqword q1 q2)
		| a, _ => a
		end.
Compute andval (bit ptr 1) (bit ptr 0).
Compute andval (bit ptr 1) (bit ptr 1).
Compute andval (byte ptr 0xFF) (byte ptr 0xF0).
Compute andval (dword ptr 0xFFFFFF) (dword ptr 0xF000FF).

Definition parityval (v : Val) : Z :=
		match v with
		| null => 0
		| bitval b => paritybit b
		| byteval b => paritybyte b
		| wordval w => parityword w
		| dwordval d => paritydword d
		| qwordval q => parityqword q
		end.

Definition signval (v : Val) : Z :=
		match v with
		| null => 0
		| bitval b => bit_to_nat b
		| byteval b => signbyte b
		| wordval w => signword w
		| dwordval d => signdword d
		| qwordval q => signqword q
		end.

Definition acmpval (v1 v2 : Val) : Z :=
		match v1, v2 with
		| null, null => 0
		| bitval b1, bitval b2 => if (Bit_eq_dec b1 b2) then 1 else 0
		| byteval b1, byteval b2 => (acmpbyte b1 b2)
		| wordval w1, wordval w2 => (acmpword w1 w2)
		| dwordval d1, dwordval d2 => (acmpdword d1 d2)
		| qwordval q1, qwordval q2 => (acmpqword q1 q2)
		| a, _ => 0
		end.

Inductive Scale := SN | S0 | S1 | S2 | S4 | S8.
Scheme Equality for Scale.
Definition nat_to_scale (n : Z) : Scale :=
		match n with
		| 0 => S0
		| 1 => S1
		| 2 => S2
		| 4 => S4
		| 8 => S8
		| _ => SN
		end.

Notation "'bit' 'ptr'" := S0 (at level 2).
Notation "'byte' 'ptr'" := S1 (at level 2).
Notation "'word' 'ptr'" := S2 (at level 2).
Notation "'dword' 'ptr'" := S4 (at level 2).
Notation "'qword' 'ptr'" := S8 (at level 2).
Check bit ptr.
Check byte ptr.
Check word ptr 10.

Definition pushval (s : Stack)(v : Val) : Stack :=
		match v with
		| null => s
		| bitval a => s
		| byteval a => push_byte s a
		| wordval a => push_word s a
		| dwordval a => push_dword s a
		| qwordval a => push_qword s a
		end.
Definition popval (s : Stack)(sc : Scale) : Stack :=
		match sc with
		| SN => s
		| S0 => s
		| S1 => pop_byte s
		| S2 => pop_word s
		| S4 => pop_dword s
		| S8 => pop_qword s
		end.
Definition topval (s : Stack)(sc : Scale) : Val :=
		match sc with
		| SN => null
		| S0 => null
		| S1 => byteval (top_byte s)
		| S2 => wordval (top_word s)
		| S4 => dwordval (top_dword s)
		| S8 => qwordval (top_qword s)
		end.


(* Environment (For memory usage) *)

Inductive VarExt :=
| var_ext : Var -> VarExt
| eflg_ext : EFLAGS -> VarExt
| cflg_ext : CFLAGS -> VarExt.
Coercion var_ext : Var >-> VarExt.
Coercion eflg_ext : EFLAGS >-> VarExt.
Coercion cflg_ext : CFLAGS >-> VarExt.
Scheme Equality for VarExt.

Definition Env := VarExt -> Scale -> Val.
Compute Scale_eq_dec S0 S0.
Definition env0 : Env :=
	fun (v : VarExt)(s : Scale) => null.
Compute env0 EAX S8.

Definition envScale (env : Env) (v : VarExt) : Scale :=
		match env v S0 with
		| null => SN
		| bitval b => S0
		| byteval b => S1
		| wordval w => S2
		| dwordval d => S4
		| qwordval q => S8
		end.
Definition nat_to_val (n : Z)(s : Scale) : Val :=
		match s with
		| SN => null
		| S0 => bitval n
		| S1 => byteval n
		| S2 => wordval n
		| S4 => dwordval n
		| S8 => qwordval n
		end.
Compute bitval 1.

Definition val_to_nat (v : Val) : Z :=
		match v with
		| null => 0
		| bitval n => bit_to_nat n
		| byteval n => byte_to_nat n
		| wordval n => word_to_nat n
		| dwordval n => dword_to_nat n
		| qwordval n => qword_to_nat n
		end.

Definition e_init (env : Env) (v : VarExt) (s : Scale) : Env :=
		fun (y : VarExt) (s1 : Scale) =>
			if (VarExt_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then nat_to_val 0 s
				else (env v s)
			else (env y s).
Definition e_test (env : Env) (v : VarExt) (x : Z) : Env :=
		fun (y : VarExt) (s : Scale) =>
		  if (VarExt_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then null
				else env v S0
			else if (VarExt_eq_dec y ZF) (* Set Zero Flag *)
				then if (Val_eq_dec (env y s) null)
					then env ZF S0
					else if (Z.eqb x 0) then nat_to_val 1 S0 else nat_to_val 0 S0
				else if (VarExt_eq_dec y PF) (* Set parity flag *)
					then if (Val_eq_dec (env y s) null)
						then env PF S0
						else if (Z.eqb (parityval (nat_to_val x (envScale env v))) 1) then nat_to_val 1 S0 else nat_to_val 0 S0
					else if (VarExt_eq_dec y SF) (* Sign flag *)
						then if (Val_eq_dec (env y s) null)
							then env SF S0
							else if (Z.eqb (signval (nat_to_val x (envScale env v))) 1) then nat_to_val 1 S0 else nat_to_val 0 S0
					else env y s.

Compute (nat_to_val 10 S2).
Compute (nat_to_val ((val_to_nat (nat_to_val 10 S2)) - (val_to_nat (nat_to_val 10 S1))) S1).
Definition e_update (env : Env) (v : VarExt) (x : Z) : Env :=
		fun (y : VarExt) (s : Scale) =>
		  if (VarExt_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then null
				else nat_to_val x (envScale env v)
			else if (VarExt_eq_dec y ZF) (* Set Zero Flag *)
				then if (Val_eq_dec (env y s) null)
					then env ZF S0
					else if (Z.eqb x 0) then nat_to_val 1 S0 else nat_to_val 0 S0
				else if (VarExt_eq_dec y PF) (* Set parity flag *)
					then if (Val_eq_dec (env y s) null)
						then env PF S0
						else if (Z.eqb (parityval (nat_to_val x (envScale env v))) 1) then nat_to_val 1 S0 else nat_to_val 0 S0
					else if (VarExt_eq_dec y SF) (* Sign flag *)
						then if (Val_eq_dec (env y s) null)
							then env SF S0
							else if (Z.eqb (signval (nat_to_val x (envScale env v))) 1) then nat_to_val 1 S0 else nat_to_val 0 S0
			else if (VarExt_eq_dec v EAX) then
				if (VarExt_eq_dec y AX) then (nat_to_val x S2)
				else if (VarExt_eq_dec y AL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y AH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v EBX) then
				if (VarExt_eq_dec y BX) then (nat_to_val x S2)
				else if (VarExt_eq_dec y BL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y BH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v ECX) then
				if (VarExt_eq_dec y CX) then (nat_to_val x S2)
				else if (VarExt_eq_dec y CL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y CH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v ECX) then
				if (VarExt_eq_dec y CX) then (nat_to_val x S2)
				else if (VarExt_eq_dec y CL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y CH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			
			else if (VarExt_eq_dec v AX) then
				if (VarExt_eq_dec y AL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y AH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v BX) then
				if (VarExt_eq_dec y BL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y BH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v CX) then
				if (VarExt_eq_dec y CL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y CH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s
			else if (VarExt_eq_dec v DX) then
				if (VarExt_eq_dec y DL) then (nat_to_val x S1)
				else if (VarExt_eq_dec y DH) then (nat_to_val ((val_to_nat (nat_to_val x S2)) / 8) S1)
				else env y s

			else if (VarExt_eq_dec v ESI) then
				if (VarExt_eq_dec y SI) then (nat_to_val x S2) else env y s
			else if (VarExt_eq_dec v EDI) then
				if (VarExt_eq_dec y DI) then (nat_to_val x S2) else env y s
			else if (VarExt_eq_dec v EBP) then
				if (VarExt_eq_dec y BP) then (nat_to_val x S2) else env y s
			else env y s.

Definition e_free (env : Env) (v : VarExt) : Env :=
		fun (y : VarExt) (s : Scale) =>
			if (VarExt_eq_dec y v)
			then null
			else env y s.

Compute env0 EAX S0.
Definition env1 := e_init env0 EAX S8.
Compute env1 EAX S0.
Compute env1 "x" S0.
Definition env2 := e_update env1 EAX (0xFFFFFFFF).
Compute env2 EAX S0.
Compute env2 "x" S0.
Definition env21 := e_init env2 "x" S1.
Definition env3 := e_update env21 "x" 0x0001.
Compute env3 "x" S0.
Compute env3 EAX S0.
Definition env4 := e_free env3 EAX.
Compute env4 "x" S0.
Compute env4 EAX S0.

Compute val_to_nat (env2 "x" S0).


(* Memory *)

Definition Memory := QWord -> Var.
Definition mem0 : Memory :=
		fun (q : QWord) => vnull.
Check mem0 0.
Compute mem0 0.

Definition mem_init (mem : Memory) (q : QWord) (v : Var) : Memory :=
		fun (q' : QWord) =>
			if (QWord_eq_dec q q')
			then if (Var_eq_dec (mem q) vnull)
				then v
				else vnull
			else (mem q').
Definition mem1 := mem_init mem0 100 "x".
Compute mem1 100.

Definition mem_update (mem : Memory) (q : QWord) (v : Var) : Memory :=
		fun (q' : QWord) =>
		  if (QWord_eq_dec q q')
			then if (Var_eq_dec (mem q) vnull)
				then vnull
				else v
			else (mem q').
Definition mem2 := mem_update mem1 100 "y".
Compute mem2 100.

Definition mem_free (mem : Memory) (q : QWord) : Memory :=
		fun (q' : QWord) =>
			if (QWord_eq_dec q q')
			then vnull
			else mem q'.
Definition mem3 := mem_free mem2 100.
Compute mem3 100.

(* Map *)

Definition Map := Var -> QWord.
Definition map0 : Map :=
		fun (s : Var) => 0.
Compute map0 EAX.

Definition map_init (map : Map) (q : QWord) (v : Var) : Map :=
		fun (v' : Var) =>
			if (Var_eq_dec v v')
			then if (QWord_eq_dec (map v) 0)
				then q
				else (map v)
			else (map v').
Compute map0 "x".
Definition map1 := map_init map0 10 "x".
Compute map1 "x".

Definition map_update (map : Map) (q : QWord) (v : Var) : Map :=
		fun (v' : Var) =>
		  if (Var_eq_dec v v')
			then if (QWord_eq_dec (map v) 0)
				then 0
				else q
			else (map v').
Definition map2 := map_update map1 100 "x".
Compute map2 "x".

Definition map_free (map : Map) (v : Var) : Map :=
		fun (v' : Var) =>
			if (Var_eq_dec v v')
			then 0
			else map v'.
Definition map3 := map_free map2 "x".
Compute map3 "x".

(* Memory Expression *)

Inductive Exp :=
| e_const : Z -> Exp
| e_var : Var -> Exp
| e_sum : Exp -> Exp -> Exp
| e_dif : Exp -> Exp -> Exp
| e_mul : Exp -> Exp -> Exp
| e_div : Exp -> Exp -> Exp.

Coercion e_const : Z >-> Exp.
Coercion e_var : Var >-> Exp.

Notation "E1 +' E2" := (e_sum E1 E2)(at level 20).
Notation "E1 -' E2" := (e_dif E1 E2)(at level 20).
Notation "E1 *' E2" := (e_mul E1 E2)(at level 20).
Notation "E1 /' E2" := (e_div E1 E2)(at level 20).

Fixpoint e_eval (e : Exp)(map : Map)(env : Env) : Z :=
		match e with
		| e_const n => n
		| e_var v =>
			match v with
			| vnull => 0
			| reg r => val_to_nat (env r S0)
			| str s => qword_to_nat (map s)
			end
		| e_sum e1 e2 => (e_eval e1 map env) + qword_to_nat (e_eval e2 map env)
		| e_dif e1 e2 => (e_eval e1 map env) - qword_to_nat (e_eval e2 map env)
		| e_mul e1 e2 => (e_eval e1 map env) * qword_to_nat (e_eval e2 map env)
		| e_div e1 e2 => (e_eval e1 map env) / qword_to_nat (e_eval e2 map env)
		end.

Compute env3 EAX S0.
Definition m1 := mem_init mem0 1 "x".
Compute m1 (e_eval (1) map1 env3).
Compute (e_eval ("x") map1 env3).

Inductive Any := var (v : Var) | val (v : Val) | exp (e : Exp).
Coercion var : Var >-> Any.
Coercion val : Val >-> Any.

Notation "'[' Exp ']'" := (exp Exp)(at level 3).

Definition a_eval (a : Any)(mem : Memory)(map : Map)(env : Env) : Z :=
		match a with
		| var v => val_to_nat (env v S0)
		| val v => val_to_nat v
		| exp e => val_to_nat (env (mem (e_eval e map env)) S0)
		end.
Definition anyScale (a : Any)(env : Env) : Scale :=
		match a with
		| var v => envScale env (var_ext v)
		| val v =>
			match v with
			| null => SN
			| bit ptr _ => S0
			| byte ptr _ => S1
			| word ptr _ => S2
			| dword ptr _ => S4
			| _ => S8
			end
		| exp e => S8
		end.

Definition map' := map_init map0 1 "x".
Definition mem' := mem_init mem0 1 "x".
Compute (e_eval (a_eval ["x"] mem' map' env3) map' env3).
Compute mem' (e_eval (a_eval ["x"] mem' map' env3) map' env3).
Inductive Instruction :=
| sequence : Instruction -> Instruction -> Instruction
| lsequence : string -> Instruction -> Instruction

| op_nop : Instruction
| op_end : Instruction
| op_mov : Var -> Any -> Instruction

| op_add : Var -> Any -> Instruction
| op_sub : Var -> Any -> Instruction
| op_mul : Var -> Any -> Instruction
| op_div : Var -> Any -> Instruction

| op_inc : Var -> Instruction
| op_dec : Var -> Instruction

| op_xchg : Var -> Var -> Instruction

| op_shr : Var -> Instruction
| op_shl : Var -> Instruction
| op_sar : Var -> Instruction
| op_sal : Var -> Instruction
| op_ror : Var -> Instruction
| op_rol : Var -> Instruction
| op_not : Var -> Instruction
| op_neg : Var -> Instruction

| op_and : Var -> Any -> Instruction
| op_nand : Var -> Any -> Instruction
| op_xand : Var -> Any -> Instruction
| op_xnand : Var -> Any -> Instruction
| op_or : Var -> Any -> Instruction
| op_nor : Var -> Any -> Instruction
| op_xor : Var -> Any -> Instruction
| op_xnor : Var -> Any -> Instruction

| op_def : string -> Scale -> Instruction
| op_free : string -> Instruction

| op_push : Var -> Instruction
| op_pop : Var -> Instruction
| op_call : string -> Instruction
| op_ret : Instruction

| op_cmp : Any -> Any -> Instruction
| op_test : Any -> Any -> Instruction
| op_jmp : string -> Instruction
| op_je : string -> Instruction
| op_jne : string -> Instruction
| op_jg : string -> Instruction
| op_jge : string -> Instruction
| op_jl : string -> Instruction
| op_jle : string -> Instruction

| op_jb : string -> Instruction
| op_jbe : string -> Instruction
| op_ja : string -> Instruction
| op_jae : string -> Instruction

| op_jz : string -> Instruction
| op_jnz : string -> Instruction
| op_jp : string -> Instruction
| op_jnp : string -> Instruction
| op_js : string -> Instruction
| op_jns : string -> Instruction
.

Notation "A ';' B" := (sequence A B) (at level 9, right associativity).
Notation "A ';'" := (sequence A op_nop) (at level 9).
Notation "A ':' B" := (lsequence A B) (at level 9, right associativity).
Notation "'nop'" := (op_nop)(at level 6).
Notation "'mov' A B" := (op_mov A B)(at level 6, A, B at level 5).

Notation "'add' A B" := (op_add A B)(at level 6, A, B at level 5).
Notation "'sub' A B" := (op_sub A B)(at level 6, A, B at level 5).
Notation "'mul' A B" := (op_mul A B)(at level 6, A, B at level 5).
Notation "'div' A B" := (op_div A B)(at level 6, A, B at level 5).

Notation "'inc' A" := (op_inc A)(at level 6, A at level 5).
Notation "'dec' A" := (op_dec A)(at level 6, A at level 5).

Notation "'xchg' A B" := (op_xchg A B)(at level 6, A, B at level 5).

Notation "'shr' A" := (op_shr A)(at level 6, A at level 5).
Notation "'shl' A" := (op_shl A)(at level 6, A at level 5).
Notation "'sar' A" := (op_sar A)(at level 6, A at level 5).
Notation "'sal' A" := (op_sal A)(at level 6, A at level 5).
Notation "'ror' A" := (op_ror A)(at level 6, A at level 5).
Notation "'rol' A" := (op_rol A)(at level 6, A at level 5).
Notation "'not' A" := (op_not A)(at level 6, A at level 5).
Notation "'neg' A" := (op_neg A)(at level 6, A at level 5).

Notation "'and' A B" := (op_and A B)(at level 6, A, B at level 5).
Notation "'nand' A B" := (op_nand A B)(at level 6, A, B at level 5).
Notation "'xand' A B" := (op_xand A B)(at level 6, A, B at level 5).
Notation "'xnand' A B" := (op_xnand A B)(at level 6, A, B at level 5).
Notation "'or' A B" := (op_or A B)(at level 6, A, B at level 5).
Notation "'nor' A B" := (op_nor A B)(at level 6, A, B at level 5).
Notation "'xor' A B" := (op_xor A B)(at level 6, A, B at level 5).
Notation "'xnor' A B" := (op_xnor A B)(at level 6, A, B at level 5).

Notation "'def' A S" := (op_def A S)(at level 6, A, S at level 5).
Notation "'free' A" := (op_free A)(at level 6, A at level 5).

Notation "'push' A" := (op_push A)(at level 6, A at level 5).
Notation "'pop' A" := (op_pop A)(at level 6, A at level 5).

Notation "'call' A" := (op_call A)(at level 6, A at level 5).
Notation "'ret'" := (op_ret)(at level 6).

Notation "'cmp' A B" := (op_cmp A B)(at level 6, A, B at level 5).
Notation "'test' A B" := (op_test A B)(at level 6, A, B at level 5).
Notation "'jmp' A" := (op_jmp A)(at level 6, A at level 5).
Notation "'je' A" := (op_je A)(at level 6, A at level 5).
Notation "'jne' A" := (op_jne A)(at level 6, A at level 5).
Notation "'jg' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jnle' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jge' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jnl' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jl' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jnge' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jle' A" := (op_jle A)(at level 6, A at level 5).
Notation "'jng' A" := (op_jle A)(at level 6, A at level 5).

Notation "'jb' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jnae' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jbe' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jna' A" := (op_jge A)(at level 6, A at level 5).
Notation "'ja' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jnbe' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jae' A" := (op_jle A)(at level 6, A at level 5).
Notation "'jnb' A" := (op_jle A)(at level 6, A at level 5).

Notation "'jz' A" := (op_jz A)(at level 6, A at level 5).
Notation "'jnz' A" := (op_jnz A)(at level 6, A at level 5).
Notation "'jp' A" := (op_jp A)(at level 6, A at level 5).
Notation "'jnp' A" := (op_jnp A)(at level 6, A at level 5).
Notation "'js' A" := (op_js A)(at level 6, A at level 5).
Notation "'jns' A" := (op_jns A)(at level 6, A at level 5).

Notation "'NOP'" := (op_nop)(at level 6).
Notation "'MOV' A B" := (op_mov A B)(at level 6, A, B at level 5).
Notation "'ADD' A B" := (op_add A B)(at level 6, A, B at level 5).
Notation "'SUB' A B" := (op_sub A B)(at level 6, A, B at level 5).
Notation "'MUL' A B" := (op_mul A B)(at level 6, A, B at level 5).
Notation "'DIV' A B" := (op_div A B)(at level 6, A, B at level 5).

Notation "'INC' A" := (op_inc A)(at level 6, A at level 5).
Notation "'DEC' A" := (op_dec A)(at level 6, A at level 5).

Notation "'XCHG' A B" := (op_xchg A B)(at level 6, A, B at level 5).

Notation "'SHR' A" := (op_shr A)(at level 6, A at level 5).
Notation "'SHL' A" := (op_shl A)(at level 6, A at level 5).
Notation "'SAR' A" := (op_sar A)(at level 6, A at level 5).
Notation "'SAL' A" := (op_sal A)(at level 6, A at level 5).
Notation "'ROR' A" := (op_ror A)(at level 6, A at level 5).
Notation "'ROL' A" := (op_rol A)(at level 6, A at level 5).
Notation "'NOT' A" := (op_not A)(at level 6, A at level 5).
Notation "'NEG' A" := (op_neg A)(at level 6, A at level 5).

Notation "'AND' A B" := (op_and A B)(at level 6, A, B at level 5).
Notation "'NAND' A B" := (op_nand A B)(at level 6, A, B at level 5).
Notation "'XAND' A B" := (op_xand A B)(at level 6, A, B at level 5).
Notation "'XNAND' A B" := (op_xnand A B)(at level 6, A, B at level 5).
Notation "'OR' A B" := (op_or A B)(at level 6, A, B at level 5).
Notation "'NOR' A B" := (op_nor A B)(at level 6, A, B at level 5).
Notation "'XOR' A B" := (op_xor A B)(at level 6, A, B at level 5).
Notation "'XNOR' A B" := (op_xnor A B)(at level 6, A, B at level 5).

Notation "'DEF' A S" := (op_def A S)(at level 6, A, S at level 5).
Notation "'FREE' A" := (op_free A)(at level 6, A at level 5).

Notation "'PUSH' A" := (op_push A)(at level 6, A at level 5).
Notation "'POP' A" := (op_pop A)(at level 6, A at level 5).
Notation "'CALL' A" := (op_call A)(at level 6, A at level 5).
Notation "'RET'" := (op_ret)(at level 6).

Notation "'CMP' A B" := (op_cmp A B)(at level 6, A, B at level 5).
Notation "'TEST' A B" := (op_test A B)(at level 6, A, B at level 5).
Notation "'JMP' A" := (op_jmp A)(at level 6, A at level 5).
Notation "'JE' A" := (op_je A)(at level 6, A at level 5).
Notation "'JNE' A" := (op_jne A)(at level 6, A at level 5).
Notation "'JG' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JNLE' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JGE' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JNL' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JL' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JNGE' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JLE' A" := (op_jle A)(at level 6, A at level 5).
Notation "'JNG' A" := (op_jle A)(at level 6, A at level 5).

Notation "'JB' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JNAE' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JBE' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JNA' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JA' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JNBE' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JAE' A" := (op_jle A)(at level 6, A at level 5).
Notation "'JNB' A" := (op_jle A)(at level 6, A at level 5).

Notation "'JZ' A" := (op_jz A)(at level 6, A at level 5).
Notation "'JNZ' A" := (op_jnz A)(at level 6, A at level 5).
Notation "'JP' A" := (op_jp A)(at level 6, A at level 5).
Notation "'JNP' A" := (op_jnp A)(at level 6, A at level 5).
Notation "'JS' A" := (op_js A)(at level 6, A at level 5).
Notation "'JNS' A" := (op_jns A)(at level 6, A at level 5).

Check (mov EAX EBX).
Check (mov EAX dword ptr (10+0x00FF00FF)).
Check nop ; nop ; mov EAX EIP; def "x" word ptr; ADD "x" word ptr 10.

(* Instruction Pointer *)

Definition IPointer := QWord -> Instruction.
Definition ip0 := fun (q : QWord) => op_end.
Compute ip0 (nat_to_qword 10).

Definition IAddInstr (q : QWord)(p : IPointer)(i : Instruction) : IPointer :=
		fun (q' : QWord) =>
		  if (QWord_eq_dec q q')
			then i
			else (p q').
Definition ip1 := IAddInstr (nat_to_qword 0) ip0 (mov EAX EBX ; mov EAX EAX ;).
Compute ip1 0.


(* Labels pointer *)

Definition LPointer := string -> Z.
Definition lp0 := fun (l : string) => -1.
Compute lp0 "f".
Definition LAddLabel (l : LPointer)(s : string)(i : Z) :=
		fun (s' : string) =>
			if (string_beq s s')
			then i
			else (l s').
Definition lp1 := LAddLabel lp0 "_main" 10.
Compute lp1 "_main".
Compute lp1 "_while".


Compute mem2 100.
Compute env2 EAX S0.
Compute ip1 0.
Compute lp1 "_main".

Inductive State := state : Memory -> Map -> Stack -> Env -> IPointer -> LPointer -> State.
Definition s0 := state mem0 map0 stack0 env0 ip0 lp0.
Definition s1 := state mem2 map2 stack0 env2 ip1 lp1.

Definition s_mem (s : State) : Memory :=
		match s with
		| state m m' st e ip lp => m
		end.
Definition s_map (s : State) : Map :=
		match s with
		| state m m' st e ip lp => m'
		end.
Definition s_stack (s : State) : Stack :=
		match s with
		| state m m' st e ip lp => st
		end.
Definition s_env (s : State) : Env :=
		match s with
		| state m m' st e ip lp => e
		end.
Definition s_ip (s : State) : IPointer :=
		match s with
		| state m m' st e ip lp => ip
		end.
Definition s_lp (s : State) : LPointer :=
		match s with
		| state m m' st e ip lp => lp
		end.

Compute (s_mem s1) 100.
Compute (s_env s1) EAX S0.
Compute (s_ip s1) 0.
Compute (s_lp s1) "_main".


Fixpoint makeState (s : State)(i : Instruction)(q : QWord) : State :=
		match s with
		| state m m' st e ip lp =>
			match i with
			| sequence s1 s2 => makeState (makeState s s1 q) s2 (sumqword q 1)
			| lsequence s1 s2 => makeState (state m m' st e ip (LAddLabel lp s1 (qword_to_nat q))) s2 q
			| op_mov a1 a2 => state m m' st e (IAddInstr q ip (op_mov a1 a2)) lp
			| op_nop => state m m' st e (IAddInstr q ip (op_nop)) lp
			| op_end => s

			| op_add a1 a2 => state m m' st e (IAddInstr q ip (op_add a1 a2)) lp
			| op_sub a1 a2 => state m m' st e (IAddInstr q ip (op_sub a1 a2)) lp
			| op_mul a1 a2 => state m m' st e (IAddInstr q ip (op_mul a1 a2)) lp
			| op_div a1 a2 => state m m' st e (IAddInstr q ip (op_div a1 a2)) lp

			| op_inc a => state m m' st e (IAddInstr q ip (op_inc a)) lp
			| op_dec a => state m m' st e (IAddInstr q ip (op_dec a)) lp
			| op_xchg a1 a2 => state m m' st e (IAddInstr q ip (op_xchg a1 a2)) lp

			| op_shr a => state m m' st e (IAddInstr q ip (op_shr a)) lp
			| op_shl a => state m m' st e (IAddInstr q ip (op_shl a)) lp
			| op_sar a => state m m' st e (IAddInstr q ip (op_sar a)) lp
			| op_sal a => state m m' st e (IAddInstr q ip (op_sal a)) lp
			| op_ror a => state m m' st e (IAddInstr q ip (op_ror a)) lp
			| op_rol a => state m m' st e (IAddInstr q ip (op_rol a)) lp
			| op_not a => state m m' st e (IAddInstr q ip (op_not a)) lp
			| op_neg a => state m m' st e (IAddInstr q ip (op_neg a)) lp

			| op_and a1 a2 => state m m' st e (IAddInstr q ip (op_and a1 a2)) lp
			| op_nand a1 a2 => state m m' st e (IAddInstr q ip (op_nand a1 a2)) lp
			| op_xand a1 a2 => state m m' st e (IAddInstr q ip (op_xand a1 a2)) lp
			| op_xnand a1 a2 => state m m' st e (IAddInstr q ip (op_xnand a1 a2)) lp
			| op_or a1 a2 => state m m' st e (IAddInstr q ip (op_or a1 a2)) lp
			| op_nor a1 a2 => state m m' st e (IAddInstr q ip (op_nor a1 a2)) lp
			| op_xor a1 a2 => state m m' st e (IAddInstr q ip (op_xor a1 a2)) lp
			| op_xnor a1 a2 => state m m' st e (IAddInstr q ip (op_xnor a1 a2)) lp

			| op_def v s => state m m' st e (IAddInstr q ip (op_def v s)) lp
			| op_free v => state m m' st e (IAddInstr q ip (op_free v)) lp

			| op_push a => state m m' st e (IAddInstr q ip (op_push a)) lp
			| op_pop a => state m m' st e (IAddInstr q ip (op_pop a)) lp
			| op_call a => state m m' st e (IAddInstr q ip (op_call a)) lp
			| op_ret => state m m' st e (IAddInstr q ip (op_ret)) lp

			| op_cmp a1 a2 => state m m' st e (IAddInstr q ip (op_cmp a1 a2)) lp
			| op_test a1 a2 => state m m' st e (IAddInstr q ip (op_test a1 a2)) lp
			| op_jmp a => state m m' st e (IAddInstr q ip (op_jmp a)) lp
			| op_je a => state m m' st e (IAddInstr q ip (op_je a)) lp
			| op_jne a => state m m' st e (IAddInstr q ip (op_jne a)) lp
			| op_jg a => state m m' st e (IAddInstr q ip (op_jg a)) lp
			| op_jge a => state m m' st e (IAddInstr q ip (op_jge a)) lp
			| op_jl a => state m m' st e (IAddInstr q ip (op_jl a)) lp
			| op_jle a => state m m' st e (IAddInstr q ip (op_jle a)) lp

			| op_jb a => state m m' st e (IAddInstr q ip (op_jb a)) lp
			| op_jbe a => state m m' st e (IAddInstr q ip (op_jbe a)) lp
			| op_ja a => state m m' st e (IAddInstr q ip (op_jae a)) lp
			| op_jae a => state m m' st e (IAddInstr q ip (op_jae a)) lp

			| op_jz a => state m m' st e (IAddInstr q ip (op_jz a)) lp
			| op_jnz a => state m m' st e (IAddInstr q ip (op_jnz a)) lp
			| op_jp a => state m m' st e (IAddInstr q ip (op_jp a)) lp
			| op_jnp a => state m m' st e (IAddInstr q ip (op_jnp a)) lp
			| op_js a => state m m' st e (IAddInstr q ip (op_js a)) lp
			| op_jns a => state m m' st e (IAddInstr q ip (op_jns a)) lp
			end
		end.


Definition p0 :=
(
"fun":
mov EAX ECX;
ret;

"_main":
mov EAX EBX;
ADD EAX dword ptr 10;
def "x" word ptr;
mov "x" AX;
xor EDX EDX;

"_for":
mov ECX "x";
dec "x";
cmp "x" EDX;
jg "_for";
call "fun"
).
Definition s0' := makeState s0 p0 0.
Compute (s_ip s0') 4.
Compute (s_lp s0') "_for".


Definition env_aux0 := e_init env0 EAX S4.
Definition env_aux1 := e_init env_aux0 EBX S4.
Definition env_aux2 := e_init env_aux1 ECX S4.
Definition env_aux3 := e_init env_aux2 EDX S4.

Definition env_aux4 := e_init env_aux3 AX S2.
Definition env_aux5 := e_init env_aux4 BX S2.
Definition env_aux6 := e_init env_aux5 CX S2.
Definition env_aux7 := e_init env_aux6 DX S2.

Definition env_aux8 := e_init env_aux7 AH S1.
Definition env_aux9 := e_init env_aux8 BH S1.
Definition env_aux10 := e_init env_aux9 CH S1.
Definition env_aux11 := e_init env_aux10 DH S1.

Definition env_aux12 := e_init env_aux11 AL S1.
Definition env_aux13 := e_init env_aux12 BL S1.
Definition env_aux14 := e_init env_aux13 CL S1.
Definition env_aux15 := e_init env_aux14 DL S1.

Definition env_aux16 := e_init env_aux15 ESI S4.
Definition env_aux17 := e_init env_aux16 EDI S4.
Definition env_aux18 := e_init env_aux17 EBP S4.
Definition env_aux19 := e_init env_aux18 ESP S4.
Definition env_aux20 := e_init env_aux19 EIP S4.

Definition env_aux21 := e_init env_aux20 SI S2.
Definition env_aux22 := e_init env_aux21 DI S2.
Definition env_aux23 := e_init env_aux22 BP S2.
Definition env_aux24 := e_init env_aux23 SP S2.

Definition env_aux25 := e_init env_aux24 CF S0.
Definition env_aux26 := e_init env_aux25 PF S0.
Definition env_aux27 := e_init env_aux26 AF S0.
Definition env_aux28 := e_init env_aux27 ZF S0.
Definition env_aux29 := e_init env_aux28 SF S0.
Definition env_aux30 := e_init env_aux29 OF S0.

Definition env_aux31 := e_init env_aux30 EF S0.
Definition env_aux32 := e_init env_aux31 GF S0.
Definition env_aux33 := e_init env_aux32 BF S0.

Compute env_aux33 EAX S0.
Definition env' := e_update (env_aux33) EAX 0xAFAFAF.
Compute env' EAX S0.
Compute env' AX S0.
Compute env' AH S0.
Compute env' AL S0.
Definition env'' := e_update (env') "x" 10.
Compute env'' AH S0.

Definition env := env_aux33.
Definition mem := mem0.
Definition map := map0.
Definition stack := stack0.
Definition ip := ip0.
Definition lp := lp0.


Inductive Gas :=
| O : Gas
| G : Gas -> Gas.

Local Open Scope nat.
Fixpoint nat_to_gas (n : nat) : Gas :=
		match n with
		| 0 => O
		| S n' => G (nat_to_gas n')
		end.
Compute nat_to_gas 10.

Local Open Scope Z_scope.
Fixpoint gas_to_nat (g : Gas) : Z :=
		match g with
		| O => 0
		| G n' => 1 + gas_to_nat (n')
		end.
Compute env3 "x" S0.
Definition e := e_update env3 "x" 10.
Fixpoint eval (s : State)(q : QWord)(gas : Gas)(mp : Z) : State :=
		match gas with
		| O => s
		| G gas' =>
			match s with
			| state m m' st e ip lp =>
				match (s_ip s) q with
				| sequence s1 s2 => s
				| lsequence s1 s2 => s
				| op_end => s
				| op_nop => eval s (sumqword q 1) (gas') mp

				| op_mov a1 a2 =>
					match a2 with
					| exp ex => eval (state m m' st
													 (e_update e a1 (e_eval ex m' e))
													 ip lp) (sumqword q 1) (gas') mp
					| _ => eval (state m m' st
									 		(e_update e a1 (e_eval (a_eval a2 m m' e) m' e))
									 		ip lp) (sumqword q 1) (gas') mp
					end

				| op_add a1 a2 => eval (state m m' st
					(e_update e a1 (a_eval a1 m m' e + a_eval a2 m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_sub a1 a2 => eval (state m m' st
					(e_update e a1 (a_eval a1 m m' e - a_eval a2 m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_mul a1 a2 => eval (state m m' st
					(e_update e a1 (a_eval a1 m m' e * a_eval a2 m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_div a1 a2 => eval (state m m' st
					(e_update e a1 (a_eval a1 m m' e / a_eval a2 m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_inc a => eval (state m m' st (e_update e a (a_eval a m m' e + 1)) ip lp) (sumqword q 1) (gas') mp
				| op_dec a => eval (state m m' st (e_update e a (a_eval a m m' e - 1)) ip lp) (sumqword q 1) (gas') mp
				| op_xchg a1 a2 => eval (state m m' st
					(e_update (e_update e a1 (a_eval a2 m m' e)) a2 (a_eval a1 m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_shr a => eval (state m m' st
					(e_update e a (val_to_nat (rshiftval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_shl a => eval (state m m' st
					(e_update e a (val_to_nat (lshiftval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_sar a => eval (state m m' st
					(e_update e a (val_to_nat (rashiftval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_sal a => eval (state m m' st
					(e_update e a (val_to_nat (lashiftval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_ror a => eval (state m m' st
					(e_update e a (val_to_nat (rrotval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_rol a => eval (state m m' st
					(e_update e a (val_to_nat (lrotval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_not a => eval (state m m' st
					(e_update e a (val_to_nat (notval (nat_to_val (a_eval a m m' e) (envScale e a)))))
					ip lp) (sumqword q 1) (gas') mp

				| op_neg a => eval (state m m' st
					(e_update e a (-a_eval a m m' e))
					ip lp) (sumqword q 1) (gas') mp

				| op_and a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (andval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_nand a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (nandval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_xand a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (xandval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_xnand a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (xnandval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_or a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (orval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_nor a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (norval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_xor a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (xorval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_xnor a1 a2 => eval (state m m' st
					(e_update e a1 (val_to_nat (xnorval (nat_to_val (a_eval a1 m m' e) (envScale e a1)) ((nat_to_val (a_eval a2 m m' e) (envScale e a1)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_def a sc => eval (state
					(mem_init m mp a)
					(map_init m' mp a)
					 st
					(e_init e a sc)
					ip lp) (sumqword q 1) (gas') (mp + 1)
				| op_free a => eval (state (mem_free m (m' a)) (map_free m' a) st (e_free e a) ip lp) (sumqword q 1) (gas') mp

				| op_push a => eval (state m m'
					(pushval st (nat_to_val (a_eval a m m' e) (envScale e a)))
					e ip lp) (sumqword q 1) (gas') mp

				| op_pop a => eval (state m m'
					(popval st (envScale e a))
					(e_update e a (val_to_nat (topval st (envScale e a)))) ip lp) (sumqword q 1) (gas') mp

				| op_call f => if (Z.gtb (lp f) 0) then
					eval (state m m' (push_qword st q) e ip lp) (lp f) (gas') mp
					else eval (state m m' (push_qword st q) e ip lp) (sumqword q 1) (gas') mp
				| op_ret => eval (state m m' (pop_qword st) e ip lp) (sumqword (top_qword st) 1) (gas') mp

				| op_cmp a1 a2 => eval (state m m' st
					(e_update (
						(e_update
							(e_update e EF (if (Z.eqb (a_eval a1 m m' e) (a_eval a2 m m' e)) then 1 else 0))
						GF (if (Z.eqb (acmpval (nat_to_val (a_eval a1 m m' e) (anyScale a1 e))
														(nat_to_val (a_eval a2 m m' e) (anyScale a2 e))) 1) then 0 else 1))
					) BF (if (Z.gtb (a_eval a1 m m' e) (a_eval a2 m m' e)) then 1 else 0))
					ip lp) (sumqword q 1) (gas') mp

				| op_test a1 a2 => eval (state m m' st
					(e_test e EAX (val_to_nat (andval (nat_to_val (a_eval a1 m m' e) (anyScale a1 e)) ((nat_to_val (a_eval a2 m m' e) (anyScale a1 e)))))) ip lp)
					(sumqword q 1) (gas') mp

				| op_jmp a => eval (state m m' st e ip lp) (lp a) (gas') mp

				| op_je a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e EF S0)) btrue) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jne a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e EF S0)) bfalse) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jg a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e GF S0)) btrue) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jge a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e GF S0)) btrue) (Bit_beq (val_to_nat (e EF S0)) btrue)) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jl a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e GF S0)) bfalse) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jle a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e GF S0)) bfalse) (Bit_beq (val_to_nat (e EF S0)) btrue)) then (lp a) else (sumqword q 1)) (gas') mp


				| op_jz a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e ZF S0)) btrue) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jnz a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e ZF S0)) bfalse) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jp a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e PF S0)) btrue) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jnp a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e PF S0)) bfalse) then (lp a) else (sumqword q 1)) (gas') mp

				| op_js a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e SF S0)) btrue) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jns a => eval (state m m' st e ip lp)
					(if (Bit_beq (val_to_nat (e SF S0)) bfalse) then (lp a) else (sumqword q 1)) (gas') mp


				| op_jb a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e BF S0)) btrue) (Bit_beq (val_to_nat (e EF S0)) bfalse)) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jbe a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e BF S0)) btrue) (Bit_beq (val_to_nat (e EF S0)) btrue)) then (lp a) else (sumqword q 1)) (gas') mp

				| op_ja a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e BF S0)) bfalse) (Bit_beq (val_to_nat (e EF S0)) bfalse)) then (lp a) else (sumqword q 1)) (gas') mp

				| op_jae a => eval (state m m' st e ip lp)
					(if (orb (Bit_beq (val_to_nat (e BF S0)) bfalse) (Bit_beq (val_to_nat (e EF S0)) btrue)) then (lp a) else (sumqword q 1)) (gas') mp
				end
			end
		end.

Definition prg0 :=
mov EAX dword ptr 10;
mul EAX EAX;
mov EBX EAX;
sub EAX dword ptr 2;
div EBX dword ptr 2;
inc EBX;
jp "label";
def "x" dword ptr;
mov "x" EAX;
def "z" byte ptr;
mov "x" EBX;
mov EBX dword ptr 10;
not EBX;
"label":
def "x" word ptr;
def "y" word ptr;
and EAX word ptr 10;
xor EDX EDX;
mov EAX ["z"];
.
Compute prg0.
Definition st' := eval (makeState (state mem map stack env ip lp) prg0 0) 0 (nat_to_gas 1000) 1.
Compute val_to_nat ((s_env st') EAX S0).
Compute ((s_env st') "y" S0).
Compute qword_to_nat ((s_map st') "z").
Compute (s_stack st').
Compute val_to_nat ((s_env st') EAX S0).
Compute (s_mem st') 2.
Compute (e_eval (a_eval ["x"] mem' map' env3) map' env3).
Compute val_to_nat ((s_env st') PF S0).

Definition prg1 :=
jmp "_main";

"_fun":
mov EAX dword ptr 10;
ret;
"_fun1":
mov EAX dword ptr 11;
jmp "_l1";
"_main":
call "_fun";

"_l1":
cmp EAX dword ptr 10;
je "_fun1";
.

Definition st'' := eval (makeState (state mem map stack env ip lp) prg1 0) 0 (nat_to_gas 1000) 1.
Compute val_to_nat ((s_env st'') EAX S0).
Compute qword_to_nat (top_qword (s_stack st'')).
Compute (s_env st'') EF S0.

Definition prg2 :=
MOV EAX dword ptr 0;
dec EAX;
test EAX dword ptr 0;
sar EAX;
.

Definition st1 := eval (makeState (state mem map stack env ip lp) prg2 0) 0 (nat_to_gas 1000) 1.
Compute ((s_env st1) EAX S0).
Compute (s_env st1) SF S0.
Compute (s_env st1) PF S0.
Compute (s_env st1) ZF S0.
End SASM.






















(* Another programming language *)
Require Import String.
Require Import Coq.Bool.Bool.
Open Scope string.
Inductive PVal :=
| pnull
| integer : Z -> PVal
| boolean : bool -> PVal.
Coercion integer : Z >-> PVal.
Coercion boolean : bool >-> PVal.

Definition PVal_to_nat (pv : PVal) : Z :=
		match pv with
		| pnull => 0
		| integer v => v
		| boolean v => if (v) then 1 else 0
		end.
Definition PVal_to_bool (pv : PVal) : bool :=
		match pv with
		| pnull => false
		| integer v => if (Z.eqb v 0) then false else true
		| boolean v => if (v) then true else false
		end.

Inductive PVar :=
| s : string -> PVar.
Coercion s : string >-> PVar.
Scheme Equality for PVar.
Compute "x".

Inductive VarType := INT | BOOL.

Definition PEnv := PVar -> PVal.

Definition pupdate (env : PEnv) (x : PVar) (v : PVal) : PEnv :=
  fun y => if (PVar_eq_dec y x)
						then v
						else (env y).

Definition penv0 := fun (var : PVar) => pnull.
Definition penv1 := pupdate penv0 "x" 10.
Definition penv2 := pupdate penv1 "y" 5.
Definition penv3 := pupdate penv2 "z" 2.


(* AExp *)

Inductive AExp :=
| avar : PVar -> AExp
| aval : PVal -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp.

Notation "A +'' B" := (aplus A B) (at level 48).
Notation "A -'' B" := (aminus A B) (at level 48).
Notation "A *'' B" := (amul A B) (at level 46).
Notation "A /'' B" := (adiv A B) (at level 46).
Coercion aval : PVal >-> AExp.
Coercion avar : PVar >-> AExp.

Compute penv1 "x".

Fixpoint aeval (aexp : AExp)(env : PEnv) : Z :=
		match aexp with
		| avar (s v) => PVal_to_nat (env v)
		| aval v =>
			match v with
			| boolean v' => if (v') then 1 else 0
			| integer v' => v'
			| _ => 0
			end
		| aplus a1 a2 => (aeval a1 env) + (aeval a2 env)
		| aminus a1 a2 => (aeval a1 env) - (aeval a2 env)
		| amul a1 a2 => (aeval a1 env) * (aeval a2 env)
		| adiv a1 a2 => (aeval a1 env) / (aeval a2 env)
		end.
Compute aeval (10+''10) penv0.
Compute aeval (10+''"x") penv1.


(* BExp *)

Inductive BExp :=
| bvar : PVar -> BExp
| bval : PVal -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blt : AExp -> AExp -> BExp
| ble : AExp -> AExp -> BExp
| bne : AExp -> AExp -> BExp
| beq : AExp -> AExp -> BExp.
Coercion bvar : PVar >-> BExp.
Coercion bval : PVal >-> BExp.


Notation "! A" := (bnot A) (at level 50).
Notation "A 'and' B" := (band A B) (at level 61).
Notation "A 'or' B" := (bor A B) (at level 62).
Notation "A != B" := (bne A B) (at level 55).
Notation "A == B" := (bne A B) (at level 55).
Notation "A <' B" := (blt A B) (at level 54).
Notation "A <=' B" := (ble A B) (at level 54).
Notation "A >' B" := (blt B A) (at level 54).
Notation "A >=' B" := (ble B A) (at level 54).

Fixpoint beval (bexp : BExp)(env : PEnv) : bool :=
		match bexp with
		| bvar v => PVal_to_bool (env v)
		| bval v =>
			match v with
			| boolean v' => if (v') then true else false
			| integer v' => if (Z.eqb v' 0) then false else true
			| _ => false
			end
		| bnot b => if (beval b env) then false else true
		| band b1 b2 => if (andb (beval b1 env) (beval b2 env)) then true else false
		| bor b1 b2 => if (orb (beval b1 env) (beval b2 env)) then true else false
		| blt a1 a2 => if (Z.ltb (aeval a1 env) (aeval a2 env)) then true else false
		| ble a1 a2 => if (Z.leb (aeval a1 env) (aeval a2 env)) then true else false
		| beq a1 a2 => if (Z.eqb (aeval a1 env) (aeval a2 env)) then true else false
		| bne a1 a2 => if (Z.eqb (aeval a1 env) (aeval a2 env)) then false else true
		end.

(* Statement for other langugage *)

Inductive Statement :=
| s_sequence : Statement -> Statement -> Statement
| s_declaration : VarType -> PVar -> Statement
| s_assignment : PVar -> AExp -> Statement
| s_if_then : BExp -> Statement -> Statement
| s_if_then_else : BExp -> Statement -> Statement -> Statement
| s_whileloop : BExp -> Statement -> Statement.

Notation "'int' X" := (s_declaration INT X) (at level 89).
Notation "'bool' X" := (s_declaration BOOL X) (at level 89).
Notation "X ::= A" := (s_assignment X A) (at level 100).
Notation "S1 ;; S2" := (s_sequence S1 S2) (at level 101, right associativity).
Notation "'doif' '(' B ')' '(' S ')'" := (s_if_then B S) (at level 100).
Notation "'doif' '(' B ')' '(' S1 ')' 'doelse' '(' S2 ')'" := (s_if_then_else B S1 S2) (at level 100).
Notation "'while' '(' B ')' '(' S ')'" := (s_whileloop B S) (at level 100).


Fixpoint peval (st : Statement)(env : PEnv)(gas : Gas) : PEnv :=
		match gas with
		| O => env
		| G gas' =>
			match st with
			| s_sequence s1 s2 => peval s2 (peval s1 env gas') gas'
			| s_declaration type x =>
					match type with
					| BOOL => pupdate env x false
					| INT => pupdate env x 0
					end
			| s_assignment a1 a2 => pupdate env a1 (aeval a2 env)
			| s_if_then b a => if (beval b env) then peval a env gas' else env
			| s_if_then_else b a1 a2 => if (beval b env) then peval a1 env gas' else peval a2 env gas'
			| s_whileloop b a => if (beval b env)
													then (peval (s_sequence a (s_whileloop b a)) env gas')
													else env
			end
		end.

Definition pprg0 :=
int "y";;
int "x";;
while ("y" <' 10)
(
	"x" ::= "x" +'' 9 *'' 4;;
	"y" ::= "y" +'' 1
).


Notation "'bit' 'ptr' A" := (bitval A)(at level 2, A at level 1).
Notation "'byte' 'ptr' A" := (byteval A)(at level 2, A at level 1).
Notation "'word' 'ptr' A" := (wordval A)(at level 2, A at level 1).
Notation "'dword' 'ptr' A" := (dwordval A)(at level 2, A at level 1).
Notation "'bit' 'ptr'" := S0 (at level 2).
Notation "'byte' 'ptr'" := S1 (at level 2).
Notation "'word' 'ptr'" := S2 (at level 2).
Notation "'dword' 'ptr'" := S4 (at level 2).
Notation "'qword' 'ptr'" := S8 (at level 2).
Notation "E1 +' E2" := (e_sum E1 E2)(at level 20).
Notation "E1 -' E2" := (e_dif E1 E2)(at level 20).
Notation "E1 *' E2" := (e_mul E1 E2)(at level 20).
Notation "E1 /' E2" := (e_div E1 E2)(at level 20).

Notation "A ';' B" := (sequence A B) (at level 9, right associativity).
Notation "A ';'" := (sequence A op_nop) (at level 9).
Notation "A ':' B" := (lsequence A B) (at level 9, right associativity).
Notation "'nop'" := (op_nop)(at level 6).
Notation "'mov' A B" := (op_mov A B)(at level 6, A, B at level 5).

Notation "'add' A B" := (op_add A B)(at level 6, A, B at level 5).
Notation "'sub' A B" := (op_sub A B)(at level 6, A, B at level 5).
Notation "'mul' A B" := (op_mul A B)(at level 6, A, B at level 5).
Notation "'div' A B" := (op_div A B)(at level 6, A, B at level 5).

Notation "'inc' A" := (op_inc A)(at level 6, A at level 5).
Notation "'dec' A" := (op_dec A)(at level 6, A at level 5).

Notation "'xchg' A B" := (op_xchg A B)(at level 6, A, B at level 5).

Notation "'shr' A" := (op_shr A)(at level 6, A at level 5).
Notation "'shl' A" := (op_shl A)(at level 6, A at level 5).
Notation "'sar' A" := (op_sar A)(at level 6, A at level 5).
Notation "'sal' A" := (op_sal A)(at level 6, A at level 5).
Notation "'ror' A" := (op_ror A)(at level 6, A at level 5).
Notation "'rol' A" := (op_rol A)(at level 6, A at level 5).
Notation "'not' A" := (op_not A)(at level 6, A at level 5).
Notation "'neg' A" := (op_neg A)(at level 6, A at level 5).

Notation "'and' A B" := (op_and A B)(at level 6, A, B at level 5).
Notation "'nand' A B" := (op_nand A B)(at level 6, A, B at level 5).
Notation "'xand' A B" := (op_xand A B)(at level 6, A, B at level 5).
Notation "'xnand' A B" := (op_xnand A B)(at level 6, A, B at level 5).
Notation "'or' A B" := (op_or A B)(at level 6, A, B at level 5).
Notation "'nor' A B" := (op_nor A B)(at level 6, A, B at level 5).
Notation "'xor' A B" := (op_xor A B)(at level 6, A, B at level 5).
Notation "'xnor' A B" := (op_xnor A B)(at level 6, A, B at level 5).

Notation "'def' A S" := (op_def A S)(at level 6, A, S at level 5).
Notation "'free' A" := (op_free A)(at level 6, A at level 5).

Notation "'push' A" := (op_push A)(at level 6, A at level 5).
Notation "'pop' A" := (op_pop A)(at level 6, A at level 5).

Notation "'call' A" := (op_call A)(at level 6, A at level 5).
Notation "'ret'" := (op_ret)(at level 6).

Notation "'cmp' A B" := (op_cmp A B)(at level 6, A, B at level 5).
Notation "'test' A B" := (op_test A B)(at level 6, A, B at level 5).
Notation "'jmp' A" := (op_jmp A)(at level 6, A at level 5).
Notation "'je' A" := (op_je A)(at level 6, A at level 5).
Notation "'jne' A" := (op_jne A)(at level 6, A at level 5).
Notation "'jg' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jnle' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jge' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jnl' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jl' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jnge' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jle' A" := (op_jle A)(at level 6, A at level 5).
Notation "'jng' A" := (op_jle A)(at level 6, A at level 5).

Notation "'jb' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jnae' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jbe' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jna' A" := (op_jge A)(at level 6, A at level 5).
Notation "'ja' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jnbe' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jae' A" := (op_jle A)(at level 6, A at level 5).
Notation "'jnb' A" := (op_jle A)(at level 6, A at level 5).

Notation "'jz' A" := (op_jz A)(at level 6, A at level 5).
Notation "'jnz' A" := (op_jnz A)(at level 6, A at level 5).
Notation "'jp' A" := (op_jp A)(at level 6, A at level 5).
Notation "'jnp' A" := (op_jnp A)(at level 6, A at level 5).
Notation "'js' A" := (op_js A)(at level 6, A at level 5).
Notation "'jns' A" := (op_jns A)(at level 6, A at level 5).

Notation "'NOP'" := (op_nop)(at level 6).
Notation "'MOV' A B" := (op_mov A B)(at level 6, A, B at level 5).
Notation "'ADD' A B" := (op_add A B)(at level 6, A, B at level 5).
Notation "'SUB' A B" := (op_sub A B)(at level 6, A, B at level 5).
Notation "'MUL' A B" := (op_mul A B)(at level 6, A, B at level 5).
Notation "'DIV' A B" := (op_div A B)(at level 6, A, B at level 5).

Notation "'INC' A" := (op_inc A)(at level 6, A at level 5).
Notation "'DEC' A" := (op_dec A)(at level 6, A at level 5).

Notation "'XCHG' A B" := (op_xchg A B)(at level 6, A, B at level 5).

Notation "'SHR' A" := (op_shr A)(at level 6, A at level 5).
Notation "'SHL' A" := (op_shl A)(at level 6, A at level 5).
Notation "'SAR' A" := (op_sar A)(at level 6, A at level 5).
Notation "'SAL' A" := (op_sal A)(at level 6, A at level 5).
Notation "'ROR' A" := (op_ror A)(at level 6, A at level 5).
Notation "'ROL' A" := (op_rol A)(at level 6, A at level 5).
Notation "'NOT' A" := (op_not A)(at level 6, A at level 5).
Notation "'NEG' A" := (op_neg A)(at level 6, A at level 5).

Notation "'AND' A B" := (op_and A B)(at level 6, A, B at level 5).
Notation "'NAND' A B" := (op_nand A B)(at level 6, A, B at level 5).
Notation "'XAND' A B" := (op_xand A B)(at level 6, A, B at level 5).
Notation "'XNAND' A B" := (op_xnand A B)(at level 6, A, B at level 5).
Notation "'OR' A B" := (op_or A B)(at level 6, A, B at level 5).
Notation "'NOR' A B" := (op_nor A B)(at level 6, A, B at level 5).
Notation "'XOR' A B" := (op_xor A B)(at level 6, A, B at level 5).
Notation "'XNOR' A B" := (op_xnor A B)(at level 6, A, B at level 5).

Notation "'DEF' A S" := (op_def A S)(at level 6, A, S at level 5).
Notation "'FREE' A S" := (op_free A S)(at level 6, A, S at level 5).

Notation "'PUSH' A" := (op_push A)(at level 6, A at level 5).
Notation "'POP' A" := (op_pop A)(at level 6, A at level 5).
Notation "'CALL' A" := (op_call A)(at level 6, A at level 5).
Notation "'RET'" := (op_ret)(at level 6).

Notation "'CMP' A B" := (op_cmp A B)(at level 6, A, B at level 5).
Notation "'TEST' A B" := (op_test A B)(at level 6, A, B at level 5).
Notation "'JMP' A" := (op_jmp A)(at level 6, A at level 5).
Notation "'JE' A" := (op_je A)(at level 6, A at level 5).
Notation "'JNE' A" := (op_jne A)(at level 6, A at level 5).
Notation "'JG' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JNLE' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JGE' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JNL' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JL' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JNGE' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JLE' A" := (op_jle A)(at level 6, A at level 5).
Notation "'JNG' A" := (op_jle A)(at level 6, A at level 5).

Notation "'JB' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JNAE' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JBE' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JNA' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JA' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JNBE' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JAE' A" := (op_jle A)(at level 6, A at level 5).
Notation "'JNB' A" := (op_jle A)(at level 6, A at level 5).

Notation "'JZ' A" := (op_jz A)(at level 6, A at level 5).
Notation "'JNZ' A" := (op_jnz A)(at level 6, A at level 5).
Notation "'JP' A" := (op_jp A)(at level 6, A at level 5).
Notation "'JNP' A" := (op_jnp A)(at level 6, A at level 5).
Notation "'JS' A" := (op_js A)(at level 6, A at level 5).
Notation "'JNS' A" := (op_jns A)(at level 6, A at level 5).



Fixpoint compile (st : Statement)(env : PEnv)(s : string) : Instruction :=
		match st with
		| s_sequence s1 s2 => (compile s1 env s) ; (compile s2 (peval s1 env (nat_to_gas 100)) s)
		| s_declaration type (s x) =>
			match type with
			| BOOL => (def x bit ptr)
			| INT => (def x dword ptr)
			end
		| s_assignment (s x) y => mov x (nat_to_val (aeval y env) S4)
		| s_if_then b s1 =>
				mov EAX (if (beval b env) then dwordval 1 else dwordval 0) ;
				cmp EAX (dwordval 1) ;
				jne (s++"b") ;
				(compile s1 env (s++"a")) ;
				(s++"b"): nop
		| s_if_then_else b s1 s2 =>
				mov EAX (if (beval b env) then dwordval 1 else dwordval 0) ;
				cmp EAX (dwordval 1) ;
				jne (s++"b") ;
				(compile s1 env (s++"a")) ;
				jmp (s++"c") ;
				(s++"b"): nop;
				(compile s2 env (s++"a")) ;
				(s++"c"): nop

		| s_whileloop b s1 =>
				(s++"b"):
				mov EAX (if (beval b env) then dwordval 1 else dwordval 0) ;
				(cmp EAX (nat_to_val 1 S4)) ;
				jne (s++"c") ;
				s: nop;
				(compile s1 env (s++"a")) ;
				jmp (s++"b") ;
				(s++"c"): nop
		end.


Definition pp1 :=
(
	int "x";;
	int "y";;
	"y" ::= 10;;
	"x" ::= "y"
).
Compute (peval pp1 penv0 (nat_to_gas 1000)) "y".
Definition c1 := compile pp1 penv0 "".
Compute c1.
Compute (nop; def "x" S4).
Definition r1 := (eval (makeState (state mem map stack env ip lp) c1 0) 0 (nat_to_gas 1000) 1).

Compute val_to_nat ((s_env r1) "x" S0).
Compute ((s_env r1) "x" S0).
Compute ((s_mem r1) 2).
Compute (s_stack r1).
Compute val_to_nat ((s_env r1) EAX S0).
Compute (s_map r1) "y".
Compute val_to_nat ((s_env r1) PF S0).
Compute (s_ip r1) 4.

Definition pp2 :=
(
	int "x";;
	"x" ::= 1;;
	int "y";;
	doif ("y" >' 10) (
		"y" ::= "y" +'' 10;;
		"x" ::= 100;;
		"x" ::= 101;;
		"y" ::= 6
	) doelse (
		"y" ::= "x";;
		"x" ::= 11;;
		"x" ::= 12;;
		"y" ::= 5
	)
).
Compute (peval pp2 penv0 (nat_to_gas 1000)) "y".
Definition c2 := compile pp2 penv0 "a".
Compute c2.
Definition r2 := (eval (makeState (state mem map stack env ip lp) c2 0) 0 (nat_to_gas 1000) 1).

Compute val_to_nat ((s_env r2) "x" S0).
Compute val_to_nat ((s_env r2) EF S0).
Compute ((s_env r2) "x" S0).
Compute ((s_mem r2) 2).
Compute (s_stack r2).
Compute val_to_nat ((s_env r2) EAX S0).
Compute (s_map r2) "y".
Compute val_to_nat ((s_env r2) PF S0).
Compute (s_ip r2) 5.