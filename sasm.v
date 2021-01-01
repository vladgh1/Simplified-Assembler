Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.
Open Scope list_scope.

Inductive Bit := false | true.
Scheme Equality for Bit.
Definition bit (n : Z) : Bit :=
		match n with
		| 0 => false
		| _ => true
		end.
Coercion bit : Z >-> Bit.

Definition bit_to_nat (b : Bit) : Z :=
		match b with
		| false => 0
		| true => 1
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


(*
 * Byte - 8 Bits
 *)

Inductive Byte : Set := byte (_ _ _ _ _ _ _ _ : Bit).
Definition zero := byte 0 0 0 0 0 0 0 0.
Definition one := byte 0 0 0 0 0 0 0 1.
Scheme Equality for Byte.

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

Definition sumqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 + qword_to_nat q2).
Definition difqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 - qword_to_nat q2).
Definition mulqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 * qword_to_nat q2).
Definition divqword (q1 q2 : QWord) : QWord :=
		nat_to_qword (qword_to_nat q1 / qword_to_nat q2).

(*
 * EFLAGS
 *)

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

Inductive XCHGReg := XCHGR.
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
Compute push_word (nil) (nat_to_word 10).

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
		| b1 :: b2 :: s => word b1 b2
		end.
Definition top_dword (s : Stack) : DWord :=
		match s with
		| nil => 0
		| b :: nil => dword (word b 0) (word 0 0)
		| b1 :: b2 :: nil => dword (word b1 b2) (word 0 0)
		| b1 :: b2 :: b3 :: nil => dword (word b1 b2) (word b3 0)
		| b1 :: b2 :: b3 :: b4 :: s => dword (word b1 b2) (word b3 b4)
		end.
Definition top_qword (s : Stack) : QWord :=
		match s with
		| nil => 0
		| b :: nil => qword (dword (word b 0) (word 0 0))
										    (dword (word 0 0) (word 0 0))
		| b1 :: b2 :: nil => qword (dword (word b1 b2) (word 0 0))
															 (dword (word 0 0) (word 0 0))
		| b1 :: b2 :: b3 :: nil => qword (dword (word b1 b2) (word b3 0))
																		 (dword (word 0 0) (word 0 0))
		| b1 :: b2 :: b3 :: b4 :: nil => qword (dword (word b1 b2) (word b3 b4))
																					 (dword (word 0 0) (word 0 0))
		| b1 :: b2 :: b3 :: b4 :: b5 :: nil => qword (dword (word b1 b2) (word b3 b4))
																								 (dword (word b5 0) (word 0 0))
		| b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil => qword (dword (word b1 b2) (word b3 b4))
																											 (dword (word b5 b6) (word 0 0))
		| b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil => qword (dword (word b1 b2) (word b3 b4))
																															(dword (word b5 b6) (word b7 0))
		| b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: s => qword (dword (word b1 b2) (word b3 b4))
																																 (dword (word b5 b6) (word b7 b8))
		end.


(* Vars and Vals *)

Inductive Var :=
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


(* Environment (For memory usage) *)

Definition Env := Var -> Scale -> Val.
Compute Scale_eq_dec S0 S0.
Definition env0 : Env :=
	fun (v : Var)(s : Scale) => null.
Compute env0 EAX S8.

Definition envScale (env : Env) (v : Var) : Scale :=
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

Definition e_init (env : Env) (v : Var) (s : Scale) : Env :=
		fun (y : Var) (s1 : Scale) =>
			if (Var_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then nat_to_val 0 s
				else (env v s)
			else (env y s).
Definition e_update (env : Env) (v : Var) (x : Z) : Env :=
		fun (y : Var) (s : Scale) =>
		  if (Var_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then null
				else nat_to_val x (envScale env v)
			else env y s.
Definition e_free (env : Env) (v : Var) : Env :=
		fun (y : Var) (s : Scale) =>
			if (Var_eq_dec y v)
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

Fixpoint e_eval (e : Exp)(env : Env) : QWord :=
		match e with
		| e_const n => n
		| e_var v => val_to_nat (env v S1)
		| e_sum e1 e2 => qword_to_nat (e_eval e1 env) + qword_to_nat (e_eval e2 env)
		| e_dif e1 e2 => qword_to_nat (e_eval e1 env) - qword_to_nat (e_eval e2 env)
		| e_mul e1 e2 => qword_to_nat (e_eval e1 env) * qword_to_nat (e_eval e2 env)
		| e_div e1 e2 => qword_to_nat (e_eval e1 env) / qword_to_nat (e_eval e2 env)
		end.

Compute env3 EAX S0.
Compute (e_eval ("x" *' "x" +' 10 -' 5 +' EAX) env3).

Definition Memory := QWord -> Val.
Definition mem0 : Memory :=
		fun (mem : QWord) => nat_to_val 0 SN.
Check mem0 10.
Compute mem0 (e_eval ("x" *' "x" +' 10 -' 5 +' EAX) env3).


Definition m_init (mem : Memory) (q : QWord) (v : Val) : Memory :=
		fun (q' : QWord) =>
			if (QWord_eq_dec q q')
			then if (Val_eq_dec (mem q) null)
				then v
				else nat_to_val 0 SN
			else (mem q').
Definition mem1 := m_init mem0 100 (nat_to_val 0xFFFF S8).
Compute mem1 100.

Definition m_update (mem : Memory) (q : QWord) (v : Val) : Memory :=
		fun (q' : QWord) =>
		  if (QWord_eq_dec q q')
			then if (Val_eq_dec (mem q) null)
				then nat_to_val 0 SN
				else v
			else (mem q').
Definition mem2 := m_update mem1 100 (nat_to_val 0xFF S4).
Compute mem2 100.

Definition m_free (mem : Memory) (q : QWord) : Memory :=
		fun (q' : QWord) =>
			if (QWord_eq_dec q q')
			then nat_to_val 0 SN
			else mem q'.
Definition mem3 := m_free mem2 100.
Compute mem3 100.


Inductive Any := var (v : Var) | val (v : Val) | exp (e : Exp).
Coercion var : Var >-> Any.
Coercion val : Val >-> Any.

Definition a_eval (a : Any)(env : Env) : Z :=
		match a with
		| var v => val_to_nat (env v S0)
		| val v => val_to_nat v
		| exp e => qword_to_nat (e_eval e env)
		end.

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

| op_def : Var -> Scale -> Instruction
| op_free : Var -> Instruction

| op_push : Var -> Instruction
| op_pop : Var -> Instruction
| op_call : string -> Instruction
| op_ret : Instruction

| op_label : string -> Instruction
| op_cmp : Var -> Var -> Instruction
| op_test : Var -> Var -> Instruction
| op_jmp : string -> Instruction
| op_jne : string -> Instruction
| op_jg : string -> Instruction
| op_jge : string -> Instruction
| op_jl : string -> Instruction
| op_jle : string -> Instruction
.

Notation "A ';' B" := (sequence A B) (at level 9, right associativity).
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

Notation "A ':' " := (op_label A)(at level 55).
Notation "'cmp' A B" := (op_cmp A B)(at level 6, A, B at level 5).
Notation "'test' A B" := (op_test A B)(at level 6, A, B at level 5).
Notation "'jmp' A" := (op_jmp A)(at level 6, A at level 5).
Notation "'jne' A" := (op_jne A)(at level 6, A at level 5).
Notation "'jg' A" := (op_jg A)(at level 6, A at level 5).
Notation "'jge' A" := (op_jge A)(at level 6, A at level 5).
Notation "'jl' A" := (op_jl A)(at level 6, A at level 5).
Notation "'jle' A" := (op_jle A)(at level 6, A at level 5).

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
Notation "'JNE' A" := (op_jne A)(at level 6, A at level 5).
Notation "'JG' A" := (op_jg A)(at level 6, A at level 5).
Notation "'JGE' A" := (op_jge A)(at level 6, A at level 5).
Notation "'JL' A" := (op_jl A)(at level 6, A at level 5).
Notation "'JLE' A" := (op_jle A)(at level 6, A at level 5).

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
Definition ip1 := IAddInstr (nat_to_qword 0) ip0 (mov EAX EBX).
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

Inductive State := state : Memory -> Env -> IPointer -> LPointer -> State.
Definition s0 := state mem0 env0 ip0 lp0.
Definition s1 := state mem2 env2 ip1 lp1.

Definition s_mem (s : State) : Memory :=
		match s with
		| state m e ip lp => m
		end.
Definition s_env (s : State) : Env :=
		match s with
		| state m e ip lp => e
		end.
Definition s_ip (s : State) : IPointer :=
		match s with
		| state m e ip lp => ip
		end.
Definition s_lp (s : State) : LPointer :=
		match s with
		| state m e ip lp => lp
		end.

Compute (s_mem s1) 100.
Compute (s_env s1) EAX S0.
Compute (s_ip s1) 0.
Compute (s_lp s1) "_main".


Fixpoint makeState (s : State)(i : Instruction)(q : QWord) : State :=
		match s with
		| state m e ip lp =>
			match i with
			| sequence s1 s2 => makeState (makeState s s1 q) s2 (sumqword q 1)
			| lsequence s1 s2 => makeState (state m e (IAddInstr q ip (op_label s1)) (LAddLabel lp s1 (qword_to_nat q))) s2 (sumqword q 1)
			| op_mov a1 a2 => state m e (IAddInstr q ip (op_mov a1 a2)) lp
			| op_nop => state m e (IAddInstr q ip (op_nop)) lp
			| op_end => s

			| op_add a1 a2 => state m e (IAddInstr q ip (op_add a1 a2)) lp
			| op_sub a1 a2 => state m e (IAddInstr q ip (op_sub a1 a2)) lp
			| op_mul a1 a2 => state m e (IAddInstr q ip (op_mul a1 a2)) lp
			| op_div a1 a2 => state m e (IAddInstr q ip (op_sub a1 a2)) lp

			| op_inc a => state m e (IAddInstr q ip (op_inc a)) lp
			| op_dec a => state m e (IAddInstr q ip (op_dec a)) lp
			| op_xchg a1 a2 => state m e (IAddInstr q ip (op_xchg a1 a2)) lp
			
			| op_shr a => state m e (IAddInstr q ip (op_shr a)) lp
			| op_shl a => state m e (IAddInstr q ip (op_shl a)) lp
			| op_sar a => state m e (IAddInstr q ip (op_sar a)) lp
			| op_sal a => state m e (IAddInstr q ip (op_sal a)) lp
			| op_ror a => state m e (IAddInstr q ip (op_ror a)) lp
			| op_rol a => state m e (IAddInstr q ip (op_rol a)) lp
			| op_not a => state m e (IAddInstr q ip (op_not a)) lp
			| op_neg a => state m e (IAddInstr q ip (op_neg a)) lp
			
			| op_and a1 a2 => state m e (IAddInstr q ip (op_and a1 a2)) lp
			| op_nand a1 a2 => state m e (IAddInstr q ip (op_nand a1 a2)) lp
			| op_xand a1 a2 => state m e (IAddInstr q ip (op_xand a1 a2)) lp
			| op_xnand a1 a2 => state m e (IAddInstr q ip (op_xnand a1 a2)) lp
			| op_or a1 a2 => state m e (IAddInstr q ip (op_or a1 a2)) lp
			| op_nor a1 a2 => state m e (IAddInstr q ip (op_nor a1 a2)) lp
			| op_xor a1 a2 => state m e (IAddInstr q ip (op_xor a1 a2)) lp
			| op_xnor a1 a2 => state m e (IAddInstr q ip (op_xnor a1 a2)) lp
			
			| op_def v s => state m e (IAddInstr q ip (op_def v s)) lp
			| op_free v => state m e (IAddInstr q ip (op_free v)) lp

			| op_push a => state m e (IAddInstr q ip (op_push a)) lp
			| op_pop a => state m e (IAddInstr q ip (op_pop a)) lp
			| op_call a => state m e (IAddInstr q ip (op_call a)) lp
			| op_ret => state m e (IAddInstr q ip (op_ret)) lp
			
			| op_label a => state m e (IAddInstr q ip (op_label a)) (LAddLabel lp a (qword_to_nat q))
			| op_cmp a1 a2 => state m e (IAddInstr q ip (op_cmp a1 a2)) lp
			| op_test a1 a2 => state m e (IAddInstr q ip (op_test a1 a2)) lp
			| op_jmp a => state m e (IAddInstr q ip (op_jmp a)) lp
			| op_jne a => state m e (IAddInstr q ip (op_jne a)) lp
			| op_jg a => state m e (IAddInstr q ip (op_jg a)) lp
			| op_jge a => state m e (IAddInstr q ip (op_jge a)) lp
			| op_jl a => state m e (IAddInstr q ip (op_jl a)) lp
			| op_jle a => state m e (IAddInstr q ip (op_jle a)) lp
			end
		end.

Compute sumqword (nat_to_qword 0) 2.

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
Compute (s_ip s0') 9.

Fixpoint makeStep (st : State)(q : QWord) : State :=
		match st with
		| state m e ip lp q =>
			match ip q with
			| sequence s1 s2 => makeStep (makeStep (state m e ip lp q) q+1)
			| op_nop => makeStep (state m e ip lp (sumqword q 1))
			| op_mov a1 a2 => makeStep (state m (e_update e a1 (a_eval a2 e)) ip lp (sumqword q 1))
			end
		end.

Check s_step (s_setup mem2 env2 ip1 lp1 0).

Definition State := St -> Val.
Definition st0 : State :=
	fun (s : St) => null.
Check st0.
Compute st0 op_nop.
