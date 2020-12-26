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


(* Environment *)

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

Definition initialize (env : Env) (v : Var) (s : Scale) : Env :=
		fun (y : Var) (s1 : Scale) =>
			if (Var_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then nat_to_val 0 s
				else (env v s)
			else (env y s).
Definition update (env : Env) (v : Var) (x : Z) : Env :=
		fun (y : Var) (s : Scale) =>
		  if (Var_eq_dec v y)
			then if (Val_eq_dec (env y s) null)
				then null
				else nat_to_val x (envScale env v)
			else env y s.
Definition deinitialize (env : Env) (v : Var) : Env :=
		fun (y : Var) (s : Scale) =>
			if (Var_eq_dec y v)
			then null
			else env y s.

Compute env0 EAX S0.
Definition env1 := initialize env0 EAX S8.
Compute env1 EAX S0.
Compute env1 "x" S0.
Definition env2 := update env1 EAX (0xFFFFFFFF).
Compute env2 EAX S0.
Compute env2 "x" S0.
Definition env21 := initialize env2 "x" S1.
Definition env3 := update env21 "x" 0x0001.
Compute env3 "x" S0.
Compute env3 EAX S0.
Definition env4 := deinitialize env3 EAX.
Compute env4 "x" S0.
Compute env4 EAX S0.

Compute val_to_nat (env2 "x" S0).


(* Memory *)

Inductive MemExp :=
| envvar : Env -> Var -> MemExp.
Notation "V // E" := (envvar E V)(at level 19).

Inductive Exp :=
| esequence : Exp -> Exp
| const : Z -> Exp
| memexp : MemExp -> Exp
| sum : Exp -> Exp -> Exp
| dif : Exp -> Exp -> Exp
| mul : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion const : Z >-> Exp.
Coercion memexp : MemExp >-> Exp.

Notation "'[' E ']'" := (esequence E) (at level 21).
Notation "E1 +' E2" := (sum E1 E2)(at level 20).
Notation "E1 -' E2" := (dif E1 E2)(at level 20).
Notation "E1 *' E2" := (mul E1 E2)(at level 20).
Notation "E1 /' E2" := (div E1 E2)(at level 20).

Check ["x"//env1 +' "x"//env1].

Definition Memory := MemExp -> Val.


Inductive Any := register (r : Reg) | val (v : Val) | exp (e : Exp).
Coercion register : Reg >-> Any.
Coercion val : Val >-> Any.

Inductive Instruction :=
| sequence : Instruction -> Instruction -> Instruction

| op_nop : Instruction
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
| op_fun : string -> Instruction
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

Notation "A ';' B" := (sequence A B) (at level 10).
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
Notation "'free' A S" := (op_free A S)(at level 6, A, S at level 5).

Notation "'push' A" := (op_push A)(at level 6, A at level 5).
Notation "'pop' A" := (op_pop A)(at level 6, A at level 5).
Notation "'fun' A" := (op_sub A)(at level 6, A at level 5).
Notation "'call' A" := (op_mul A)(at level 6, A at level 5).
Notation "'ret' A" := (op_div A)(at level 6, A at level 5).

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
Notation "'FUN' A" := (op_sub A)(at level 6, A at level 5).
Notation "'CALL' A" := (op_mul A)(at level 6, A at level 5).
Notation "'RET' A" := (op_div A)(at level 6, A at level 5).

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
Definition ip0 := fun (q : QWord) => nop.
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
Definition LAddLabel (s : string)(l : LPointer)(i : Z) :=
		fun (s' : string) =>
			if (string_beq s s')
			then i
			else (l s').
Definition lp1 := LAddLabel "_main" lp0 10.
Compute lp1 "_main".
Compute lp1 "_while".


Inductive St :=
| instruction_s : Instruction -> St.
Coercion instruction_s : Instruction >-> St.

Definition State := St -> Val.
Definition st0 : State :=
	fun (s : St) => null.
Check st0.
Compute st0 op_nop.