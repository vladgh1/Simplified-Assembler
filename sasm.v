Require Import Bool.
Require Import BinPos.
Require Import Nat.

Fixpoint pow {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
 match n with
  | O   => f a
  | S n => f (pow f n a)
end.
Notation "f ^ n" := (pow f n).

Inductive Bit := bfalse | btrue.
Definition bit (n : nat) : Bit :=
	match n with
		| 0 => bfalse
		| _ => btrue
	end.
Coercion bit : nat >-> Bit.

Inductive byte : Set := Byte (_ _ _ _ _ _ _ _ : Bit).
Definition zero := Byte 0 0 0 0 0 0 0 0.
Definition one := Byte 0 0 0 0 0 0 0 1.

Definition app1 (f : Bit -> Bit) (a : byte) :=
  match a with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8 =>
      Byte (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7) (f a8)  end.

Definition app2 (f : Bit -> Bit -> Bit) (a b : byte) :=
  match a, b with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8, Byte b1 b2 b3 b4 b5 b6 b7 b8 =>
      Byte (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4)
      (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8)
  end.

Definition rshift (a : byte) :=
  match a with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8 => Byte 0 a1 a2 a3 a4 a5 a6 a7
  end.
Definition lshift (a : byte) :=
  match a with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8 => Byte a2 a3 a4 a5 a6 a7 a8 0
  end.

Definition rrot (a : byte) :=
  match a with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8 => Byte a8 a1 a2 a3 a4 a5 a6 a7
  end.
Definition lrot (a : byte) :=
  match a with
    | Byte a1 a2 a3 a4 a5 a6 a7 a8 => Byte a2 a3 a4 a5 a6 a7 a8 a1
  end.

Definition orbit (b1 b2 : Bit) : Bit :=
	match b1, b2 with
	| bfalse, bfalse => bfalse
	| _, _ => btrue
	end.

Definition eqbit (b1 b2 : Bit) : bool :=
	match b1, b2 with
	| bfalse, bfalse => true
	| btrue, btrue => true
	| _, _ => false
	end.

Fixpoint byte_from_pos_aux (res acc : byte) (z : positive)
  (n : nat) {struct n} : byte :=
  match n with
    | O => res
    | S n1 =>
      match z with
        | xH => app2 orbit res acc
        | xI z' => byte_from_pos_aux (app2 orbit res acc) (lshift acc) z' n1
        | xO z' => byte_from_pos_aux res (lshift acc) z' n1
      end
  end.

Definition byte_from_pos (a : positive) := byte_from_pos_aux zero one a 8.

Definition byte_from_nat (a : nat) :=
  match a with
    | O => zero
    | S a' => byte_from_pos (P_of_succ_nat a')
  end.

Compute byte_from_nat 10.
Definition nat_from_byte (a : byte) : nat :=
  let (a7, a6, a5, a4, a3, a2, a1, a0) := a in
    ((if (eqbit a0 btrue) then 1 else 0) * (2 ^ 0)) +
    ((if (eqbit a1 btrue) then 1 else 0) * (2 ^ 1)) +
    ((if (eqbit a2 btrue) then 1 else 0) * (2 ^ 2)) +
    ((if (eqbit a3 btrue) then 1 else 0) * (2 ^ 3)) +
    ((if (eqbit a4 btrue) then 1 else 0) * (2 ^ 4)) +
    ((if (eqbit a5 btrue) then 1 else 0) * (2 ^ 5)) +
    ((if (eqbit a6 btrue) then 1 else 0) * (2 ^ 6)) +
    ((if (eqbit a7 btrue) then 1 else 0) * (2 ^ 7)).

Definition nat_to_byte (a : nat) : byte :=
  if (a mod 2) then Byte 0 0 0 0 0 0 0 0 else 10.

Notation "A 'b'" := (byte_from_nat A)(at level 20).
Compute Byte 0 0 0 0 0 0 0 0.

Compute 10b.
Definition n := byte_of_nat 10.
Compute n.

Compute nat_of_byte n.


Check bit 1.

Inductive Word :=
| word : Byte -> Byte -> Word.

Check byte bfalse bfalse bfalse bfalse bfalse btrue btrue btrue.

Inductive Registers :=
