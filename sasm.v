Require Import Bool Coq.ZArith.BinInt.
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

Inductive XCHGReg := XCHGR.
Inductive ByteReg := AH | AL | BH | BL | CH | CL | DH | DL.
Inductive WordReg := AX | BX | CX | DX.
Inductive DWordReg := EAX | EBX | ECX | EDX | ESI | EDI | EBP.
Inductive Reg := byteReg (r : ByteReg) | wordReg (r : WordReg) | dwordReg (r : DWordReg) | ESP | EIP.

Coercion byteReg : ByteReg >-> Reg.
Coercion wordReg : WordReg >-> Reg.
Coercion dwordReg : DWordReg >-> Reg.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

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
| dwordval : DWord -> Val.
Scheme Equality for Val.

Inductive Scale := S0 | S1 | S2 | S4 | S8.
Scheme Equality for Scale.
Definition nat_to_scale (n : Z) : Scale :=
		match n with
		| 0 => S0
		| 1 => S1
		| 2 => S2
		| 4 => S4
		| 8 => S8
		| _ => S8
		end.

Definition Env := Var -> Scale -> Val.
Compute Scale_eq_dec S0 S0.
Definition env0 : Env :=
	fun (v : Var)(s : Scale) =>
		if (Scale_eq_dec s S0)
		then null
		else if (Scale_eq_dec s S1)
				 then bitval 0
				 else if (Scale_eq_dec s S2)
				 			then byteval 0
				 			else if (Scale_eq_dec s S4)
				 			then wordval 0
				 			else dwordval 0.
Check env0.
Compute env0 EAX S8.

Definition initializate (env : Env) (v : Var) (s : Scale) : Env :=
		fun (y : Var) (s1 : Scale) =>
			if (Val_eq_dec (env v S0) null)
			then (env y s)
			else (env v s).

Compute env0 EAX S0.
Definition envScale (env : Env) (v : Var) : Scale :=
		match env v S0 with
		| null => S0
		| bitval b => S1
		| byteval b => S2
		| wordval w => S4
		| dwordval d => S8
		end.
Definition nat_to_val (n : Z)(s : Scale) : Val :=
		match s with
		| S0 => null
		| S1 => bitval n
		| S2 => byteval n
		| S4 => wordval n
		| S8 => dwordval n
		end.

Compute env0 EAX S0.
Definition env1 := initializate env0 EAX S8.
Compute env1 EAX S0.

Definition update (env : Env) (x : Var) (v : Z) : Env :=
		fun (y : Var) (s : Scale) =>
		  if (Var_eq_dec y x)
		  then nat_to_val v (envScale env x)
		  else (env y (envScale env y)).
Check AX.
Definition env2 := update env1 EAX (0x0F0F).
Compute env2 EAX S0.
Compute envScale env0 EAX.


Inductive Instruction :=
| op_mov : Var -> Var -> Instruction
| op_add : Var -> Var -> Instruction
| op_sub : Var -> Var -> Instruction
| op_mul : Var -> Var -> Instruction
| op_div : Var -> Var -> Instruction

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

| op_and : Var -> Var -> Instruction
| op_nand : Var -> Var -> Instruction
| op_xand : Var -> Var -> Instruction
| op_xnand : Var -> Var -> Instruction
| op_or : Var -> Var -> Instruction
| op_nor : Var -> Var -> Instruction
| op_xor : Var -> Var -> Instruction
| op_xnor : Var -> Var -> Instruction

| op_def : Var -> Scale -> Instruction
| op_free : Var -> Instruction

| op_push : Var -> Instruction
| op_pop : Var -> Instruction
| op_fun : string -> Instruction
| op_call : string -> Instruction
| op_ret : Instruction

| op_label : string -> Instruction
| op_cmp : Var -> Var -> Instruction
| op_jmp : string -> Instruction
| op_jne : string -> Instruction
| op_jg : string -> Instruction
| op_jge : string -> Instruction
| op_jl : string -> Instruction
| op_jle : string -> Instruction
.

Notation "'mov' A B" := (op_mov A B)(at level 1, A, B at level 0).
Notation "'add' A B" := (op_add A B)(at level 1, A, B at level 0).
Notation "'sub' A B" := (op_sub A B)(at level 1, A, B at level 0).
Notation "'mul' A B" := (op_mul A B)(at level 1, A, B at level 0).
Notation "'div' A B" := (op_div A B)(at level 1, A, B at level 0).

Notation "'inc' A" := (op_inc A)(at level 1, A at level 0).
Notation "'dec' A" := (op_dec A)(at level 1, A at level 0).

Notation "'xchg' A B" := (op_xchg A B)(at level 1, A, B at level 0).

Notation "'shr' A" := (op_shr A)(at level 1, A at level 0).
Notation "'shl' A" := (op_shl A)(at level 1, A at level 0).
Notation "'sar' A" := (op_sar A)(at level 1, A at level 0).
Notation "'sal' A" := (op_sal A)(at level 1, A at level 0).
Notation "'ror' A" := (op_ror A)(at level 1, A at level 0).
Notation "'rol' A" := (op_rol A)(at level 1, A at level 0).
Notation "'not' A" := (op_not A)(at level 1, A at level 0).

Notation "'and' A B" := (op_and A B)(at level 1, A, B at level 0).
Notation "'nand' A B" := (op_nand A B)(at level 1, A, B at level 0).
Notation "'xand' A B" := (op_xand A B)(at level 1, A, B at level 0).
Notation "'xnand' A B" := (op_xnand A B)(at level 1, A, B at level 0).
Notation "'or' A B" := (op_or A B)(at level 1, A, B at level 0).
Notation "'nor' A B" := (op_nor A B)(at level 1, A, B at level 0).
Notation "'xor' A B" := (op_xor A B)(at level 1, A, B at level 0).
Notation "'xnor' A B" := (op_xnor A B)(at level 1, A, B at level 0).

Notation "'def' A S" := (op_def A S)(at level 1, A, S at level 0).
Notation "'free' A S" := (op_free A S)(at level 1, A, S at level 0).

Notation "'push' A" := (op_push A)(at level 1, A at level 0).
Notation "'pop' A" := (op_pop A)(at level 1, A at level 0).
Notation "'fun' A" := (op_sub A)(at level 1, A at level 0).
Notation "'call' A" := (op_mul A)(at level 1, A at level 0).
Notation "'ret' A" := (op_div A)(at level 1, A at level 0).

Notation "A ':' " := (op_label A)(at level 1).
Notation "'cmp' A B" := (op_cmp A B)(at level 1, A, B at level 0).
Notation "'jmp' A" := (op_jmp A)(at level 1, A at level 0).
Notation "'jne' A" := (op_jne A)(at level 1, A at level 0).
Notation "'jg' A" := (op_jg A)(at level 1, A at level 0).
Notation "'jge' A" := (op_jge A)(at level 1, A at level 0).
Notation "'jl' A" := (op_jl A)(at level 1, A at level 0).
Notation "'jle' A" := (op_jle A)(at level 1, A at level 0).
Check (mov EAX EBX).
