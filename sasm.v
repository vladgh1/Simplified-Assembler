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

Compute nat_to_byte 10.
Compute byte_to_nat (nat_to_byte 10).

Inductive bytebin :=
| b00000000
| b00000001
| b00000010
| b00000011
| b00000100
| b00000101
| b00000110
| b00000111
| b00001000
| b00001001
| b00001010
| b00001011
| b00001100
| b00001101
| b00001110
| b00001111
| b00010000
| b00010001
| b00010010
| b00010011
| b00010100
| b00010101
| b00010110
| b00010111
| b00011000
| b00011001
| b00011010
| b00011011
| b00011100
| b00011101
| b00011110
| b00011111
| b00100000
| b00100001
| b00100010
| b00100011
| b00100100
| b00100101
| b00100110
| b00100111
| b00101000
| b00101001
| b00101010
| b00101011
| b00101100
| b00101101
| b00101110
| b00101111
| b00110000
| b00110001
| b00110010
| b00110011
| b00110100
| b00110101
| b00110110
| b00110111
| b00111000
| b00111001
| b00111010
| b00111011
| b00111100
| b00111101
| b00111110
| b00111111
| b01000000
| b01000001
| b01000010
| b01000011
| b01000100
| b01000101
| b01000110
| b01000111
| b01001000
| b01001001
| b01001010
| b01001011
| b01001100
| b01001101
| b01001110
| b01001111
| b01010000
| b01010001
| b01010010
| b01010011
| b01010100
| b01010101
| b01010110
| b01010111
| b01011000
| b01011001
| b01011010
| b01011011
| b01011100
| b01011101
| b01011110
| b01011111
| b01100000
| b01100001
| b01100010
| b01100011
| b01100100
| b01100101
| b01100110
| b01100111
| b01101000
| b01101001
| b01101010
| b01101011
| b01101100
| b01101101
| b01101110
| b01101111
| b01110000
| b01110001
| b01110010
| b01110011
| b01110100
| b01110101
| b01110110
| b01110111
| b01111000
| b01111001
| b01111010
| b01111011
| b01111100
| b01111101
| b01111110
| b01111111
| b10000000
| b10000001
| b10000010
| b10000011
| b10000100
| b10000101
| b10000110
| b10000111
| b10001000
| b10001001
| b10001010
| b10001011
| b10001100
| b10001101
| b10001110
| b10001111
| b10010000
| b10010001
| b10010010
| b10010011
| b10010100
| b10010101
| b10010110
| b10010111
| b10011000
| b10011001
| b10011010
| b10011011
| b10011100
| b10011101
| b10011110
| b10011111
| b10100000
| b10100001
| b10100010
| b10100011
| b10100100
| b10100101
| b10100110
| b10100111
| b10101000
| b10101001
| b10101010
| b10101011
| b10101100
| b10101101
| b10101110
| b10101111
| b10110000
| b10110001
| b10110010
| b10110011
| b10110100
| b10110101
| b10110110
| b10110111
| b10111000
| b10111001
| b10111010
| b10111011
| b10111100
| b10111101
| b10111110
| b10111111
| b11000000
| b11000001
| b11000010
| b11000011
| b11000100
| b11000101
| b11000110
| b11000111
| b11001000
| b11001001
| b11001010
| b11001011
| b11001100
| b11001101
| b11001110
| b11001111
| b11010000
| b11010001
| b11010010
| b11010011
| b11010100
| b11010101
| b11010110
| b11010111
| b11011000
| b11011001
| b11011010
| b11011011
| b11011100
| b11011101
| b11011110
| b11011111
| b11100000
| b11100001
| b11100010
| b11100011
| b11100100
| b11100101
| b11100110
| b11100111
| b11101000
| b11101001
| b11101010
| b11101011
| b11101100
| b11101101
| b11101110
| b11101111
| b11110000
| b11110001
| b11110010
| b11110011
| b11110100
| b11110101
| b11110110
| b11110111
| b11111000
| b11111001
| b11111010
| b11111011
| b11111100
| b11111101
| b11111110
| b11111111
.

Definition bin_to_byte (b : bytebin) : Byte :=
		match b with
		 | b00000000 => byte 0 0 0 0 0 0 0 0
		 | b00000001 => byte 0 0 0 0 0 0 0 1
		 | b00000010 => byte 0 0 0 0 0 0 1 0
		 | b00000011 => byte 0 0 0 0 0 0 1 1
		 | b00000100 => byte 0 0 0 0 0 1 0 0
		 | b00000101 => byte 0 0 0 0 0 1 0 1
		 | b00000110 => byte 0 0 0 0 0 1 1 0
		 | b00000111 => byte 0 0 0 0 0 1 1 1
		 | b00001000 => byte 0 0 0 0 1 0 0 0
		 | b00001001 => byte 0 0 0 0 1 0 0 1
		 | b00001010 => byte 0 0 0 0 1 0 1 0
		 | b00001011 => byte 0 0 0 0 1 0 1 1
		 | b00001100 => byte 0 0 0 0 1 1 0 0
		 | b00001101 => byte 0 0 0 0 1 1 0 1
		 | b00001110 => byte 0 0 0 0 1 1 1 0
		 | b00001111 => byte 0 0 0 0 1 1 1 1
		 | b00010000 => byte 0 0 0 1 0 0 0 0
		 | b00010001 => byte 0 0 0 1 0 0 0 1
		 | b00010010 => byte 0 0 0 1 0 0 1 0
		 | b00010011 => byte 0 0 0 1 0 0 1 1
		 | b00010100 => byte 0 0 0 1 0 1 0 0
		 | b00010101 => byte 0 0 0 1 0 1 0 1
		 | b00010110 => byte 0 0 0 1 0 1 1 0
		 | b00010111 => byte 0 0 0 1 0 1 1 1
		 | b00011000 => byte 0 0 0 1 1 0 0 0
		 | b00011001 => byte 0 0 0 1 1 0 0 1
		 | b00011010 => byte 0 0 0 1 1 0 1 0
		 | b00011011 => byte 0 0 0 1 1 0 1 1
		 | b00011100 => byte 0 0 0 1 1 1 0 0
		 | b00011101 => byte 0 0 0 1 1 1 0 1
		 | b00011110 => byte 0 0 0 1 1 1 1 0
		 | b00011111 => byte 0 0 0 1 1 1 1 1
		 | b00100000 => byte 0 0 1 0 0 0 0 0
		 | b00100001 => byte 0 0 1 0 0 0 0 1
		 | b00100010 => byte 0 0 1 0 0 0 1 0
		 | b00100011 => byte 0 0 1 0 0 0 1 1
		 | b00100100 => byte 0 0 1 0 0 1 0 0
		 | b00100101 => byte 0 0 1 0 0 1 0 1
		 | b00100110 => byte 0 0 1 0 0 1 1 0
		 | b00100111 => byte 0 0 1 0 0 1 1 1
		 | b00101000 => byte 0 0 1 0 1 0 0 0
		 | b00101001 => byte 0 0 1 0 1 0 0 1
		 | b00101010 => byte 0 0 1 0 1 0 1 0
		 | b00101011 => byte 0 0 1 0 1 0 1 1
		 | b00101100 => byte 0 0 1 0 1 1 0 0
		 | b00101101 => byte 0 0 1 0 1 1 0 1
		 | b00101110 => byte 0 0 1 0 1 1 1 0
		 | b00101111 => byte 0 0 1 0 1 1 1 1
		 | b00110000 => byte 0 0 1 1 0 0 0 0
		 | b00110001 => byte 0 0 1 1 0 0 0 1
		 | b00110010 => byte 0 0 1 1 0 0 1 0
		 | b00110011 => byte 0 0 1 1 0 0 1 1
		 | b00110100 => byte 0 0 1 1 0 1 0 0
		 | b00110101 => byte 0 0 1 1 0 1 0 1
		 | b00110110 => byte 0 0 1 1 0 1 1 0
		 | b00110111 => byte 0 0 1 1 0 1 1 1
		 | b00111000 => byte 0 0 1 1 1 0 0 0
		 | b00111001 => byte 0 0 1 1 1 0 0 1
		 | b00111010 => byte 0 0 1 1 1 0 1 0
		 | b00111011 => byte 0 0 1 1 1 0 1 1
		 | b00111100 => byte 0 0 1 1 1 1 0 0
		 | b00111101 => byte 0 0 1 1 1 1 0 1
		 | b00111110 => byte 0 0 1 1 1 1 1 0
		 | b00111111 => byte 0 0 1 1 1 1 1 1
		 | b01000000 => byte 0 1 0 0 0 0 0 0
		 | b01000001 => byte 0 1 0 0 0 0 0 1
		 | b01000010 => byte 0 1 0 0 0 0 1 0
		 | b01000011 => byte 0 1 0 0 0 0 1 1
		 | b01000100 => byte 0 1 0 0 0 1 0 0
		 | b01000101 => byte 0 1 0 0 0 1 0 1
		 | b01000110 => byte 0 1 0 0 0 1 1 0
		 | b01000111 => byte 0 1 0 0 0 1 1 1
		 | b01001000 => byte 0 1 0 0 1 0 0 0
		 | b01001001 => byte 0 1 0 0 1 0 0 1
		 | b01001010 => byte 0 1 0 0 1 0 1 0
		 | b01001011 => byte 0 1 0 0 1 0 1 1
		 | b01001100 => byte 0 1 0 0 1 1 0 0
		 | b01001101 => byte 0 1 0 0 1 1 0 1
		 | b01001110 => byte 0 1 0 0 1 1 1 0
		 | b01001111 => byte 0 1 0 0 1 1 1 1
		 | b01010000 => byte 0 1 0 1 0 0 0 0
		 | b01010001 => byte 0 1 0 1 0 0 0 1
		 | b01010010 => byte 0 1 0 1 0 0 1 0
		 | b01010011 => byte 0 1 0 1 0 0 1 1
		 | b01010100 => byte 0 1 0 1 0 1 0 0
		 | b01010101 => byte 0 1 0 1 0 1 0 1
		 | b01010110 => byte 0 1 0 1 0 1 1 0
		 | b01010111 => byte 0 1 0 1 0 1 1 1
		 | b01011000 => byte 0 1 0 1 1 0 0 0
		 | b01011001 => byte 0 1 0 1 1 0 0 1
		 | b01011010 => byte 0 1 0 1 1 0 1 0
		 | b01011011 => byte 0 1 0 1 1 0 1 1
		 | b01011100 => byte 0 1 0 1 1 1 0 0
		 | b01011101 => byte 0 1 0 1 1 1 0 1
		 | b01011110 => byte 0 1 0 1 1 1 1 0
		 | b01011111 => byte 0 1 0 1 1 1 1 1
		 | b01100000 => byte 0 1 1 0 0 0 0 0
		 | b01100001 => byte 0 1 1 0 0 0 0 1
		 | b01100010 => byte 0 1 1 0 0 0 1 0
		 | b01100011 => byte 0 1 1 0 0 0 1 1
		 | b01100100 => byte 0 1 1 0 0 1 0 0
		 | b01100101 => byte 0 1 1 0 0 1 0 1
		 | b01100110 => byte 0 1 1 0 0 1 1 0
		 | b01100111 => byte 0 1 1 0 0 1 1 1
		 | b01101000 => byte 0 1 1 0 1 0 0 0
		 | b01101001 => byte 0 1 1 0 1 0 0 1
		 | b01101010 => byte 0 1 1 0 1 0 1 0
		 | b01101011 => byte 0 1 1 0 1 0 1 1
		 | b01101100 => byte 0 1 1 0 1 1 0 0
		 | b01101101 => byte 0 1 1 0 1 1 0 1
		 | b01101110 => byte 0 1 1 0 1 1 1 0
		 | b01101111 => byte 0 1 1 0 1 1 1 1
		 | b01110000 => byte 0 1 1 1 0 0 0 0
		 | b01110001 => byte 0 1 1 1 0 0 0 1
		 | b01110010 => byte 0 1 1 1 0 0 1 0
		 | b01110011 => byte 0 1 1 1 0 0 1 1
		 | b01110100 => byte 0 1 1 1 0 1 0 0
		 | b01110101 => byte 0 1 1 1 0 1 0 1
		 | b01110110 => byte 0 1 1 1 0 1 1 0
		 | b01110111 => byte 0 1 1 1 0 1 1 1
		 | b01111000 => byte 0 1 1 1 1 0 0 0
		 | b01111001 => byte 0 1 1 1 1 0 0 1
		 | b01111010 => byte 0 1 1 1 1 0 1 0
		 | b01111011 => byte 0 1 1 1 1 0 1 1
		 | b01111100 => byte 0 1 1 1 1 1 0 0
		 | b01111101 => byte 0 1 1 1 1 1 0 1
		 | b01111110 => byte 0 1 1 1 1 1 1 0
		 | b01111111 => byte 0 1 1 1 1 1 1 1
		 | b10000000 => byte 1 0 0 0 0 0 0 0
		 | b10000001 => byte 1 0 0 0 0 0 0 1
		 | b10000010 => byte 1 0 0 0 0 0 1 0
		 | b10000011 => byte 1 0 0 0 0 0 1 1
		 | b10000100 => byte 1 0 0 0 0 1 0 0
		 | b10000101 => byte 1 0 0 0 0 1 0 1
		 | b10000110 => byte 1 0 0 0 0 1 1 0
		 | b10000111 => byte 1 0 0 0 0 1 1 1
		 | b10001000 => byte 1 0 0 0 1 0 0 0
		 | b10001001 => byte 1 0 0 0 1 0 0 1
		 | b10001010 => byte 1 0 0 0 1 0 1 0
		 | b10001011 => byte 1 0 0 0 1 0 1 1
		 | b10001100 => byte 1 0 0 0 1 1 0 0
		 | b10001101 => byte 1 0 0 0 1 1 0 1
		 | b10001110 => byte 1 0 0 0 1 1 1 0
		 | b10001111 => byte 1 0 0 0 1 1 1 1
		 | b10010000 => byte 1 0 0 1 0 0 0 0
		 | b10010001 => byte 1 0 0 1 0 0 0 1
		 | b10010010 => byte 1 0 0 1 0 0 1 0
		 | b10010011 => byte 1 0 0 1 0 0 1 1
		 | b10010100 => byte 1 0 0 1 0 1 0 0
		 | b10010101 => byte 1 0 0 1 0 1 0 1
		 | b10010110 => byte 1 0 0 1 0 1 1 0
		 | b10010111 => byte 1 0 0 1 0 1 1 1
		 | b10011000 => byte 1 0 0 1 1 0 0 0
		 | b10011001 => byte 1 0 0 1 1 0 0 1
		 | b10011010 => byte 1 0 0 1 1 0 1 0
		 | b10011011 => byte 1 0 0 1 1 0 1 1
		 | b10011100 => byte 1 0 0 1 1 1 0 0
		 | b10011101 => byte 1 0 0 1 1 1 0 1
		 | b10011110 => byte 1 0 0 1 1 1 1 0
		 | b10011111 => byte 1 0 0 1 1 1 1 1
		 | b10100000 => byte 1 0 1 0 0 0 0 0
		 | b10100001 => byte 1 0 1 0 0 0 0 1
		 | b10100010 => byte 1 0 1 0 0 0 1 0
		 | b10100011 => byte 1 0 1 0 0 0 1 1
		 | b10100100 => byte 1 0 1 0 0 1 0 0
		 | b10100101 => byte 1 0 1 0 0 1 0 1
		 | b10100110 => byte 1 0 1 0 0 1 1 0
		 | b10100111 => byte 1 0 1 0 0 1 1 1
		 | b10101000 => byte 1 0 1 0 1 0 0 0
		 | b10101001 => byte 1 0 1 0 1 0 0 1
		 | b10101010 => byte 1 0 1 0 1 0 1 0
		 | b10101011 => byte 1 0 1 0 1 0 1 1
		 | b10101100 => byte 1 0 1 0 1 1 0 0
		 | b10101101 => byte 1 0 1 0 1 1 0 1
		 | b10101110 => byte 1 0 1 0 1 1 1 0
		 | b10101111 => byte 1 0 1 0 1 1 1 1
		 | b10110000 => byte 1 0 1 1 0 0 0 0
		 | b10110001 => byte 1 0 1 1 0 0 0 1
		 | b10110010 => byte 1 0 1 1 0 0 1 0
		 | b10110011 => byte 1 0 1 1 0 0 1 1
		 | b10110100 => byte 1 0 1 1 0 1 0 0
		 | b10110101 => byte 1 0 1 1 0 1 0 1
		 | b10110110 => byte 1 0 1 1 0 1 1 0
		 | b10110111 => byte 1 0 1 1 0 1 1 1
		 | b10111000 => byte 1 0 1 1 1 0 0 0
		 | b10111001 => byte 1 0 1 1 1 0 0 1
		 | b10111010 => byte 1 0 1 1 1 0 1 0
		 | b10111011 => byte 1 0 1 1 1 0 1 1
		 | b10111100 => byte 1 0 1 1 1 1 0 0
		 | b10111101 => byte 1 0 1 1 1 1 0 1
		 | b10111110 => byte 1 0 1 1 1 1 1 0
		 | b10111111 => byte 1 0 1 1 1 1 1 1
		 | b11000000 => byte 1 1 0 0 0 0 0 0
		 | b11000001 => byte 1 1 0 0 0 0 0 1
		 | b11000010 => byte 1 1 0 0 0 0 1 0
		 | b11000011 => byte 1 1 0 0 0 0 1 1
		 | b11000100 => byte 1 1 0 0 0 1 0 0
		 | b11000101 => byte 1 1 0 0 0 1 0 1
		 | b11000110 => byte 1 1 0 0 0 1 1 0
		 | b11000111 => byte 1 1 0 0 0 1 1 1
		 | b11001000 => byte 1 1 0 0 1 0 0 0
		 | b11001001 => byte 1 1 0 0 1 0 0 1
		 | b11001010 => byte 1 1 0 0 1 0 1 0
		 | b11001011 => byte 1 1 0 0 1 0 1 1
		 | b11001100 => byte 1 1 0 0 1 1 0 0
		 | b11001101 => byte 1 1 0 0 1 1 0 1
		 | b11001110 => byte 1 1 0 0 1 1 1 0
		 | b11001111 => byte 1 1 0 0 1 1 1 1
		 | b11010000 => byte 1 1 0 1 0 0 0 0
		 | b11010001 => byte 1 1 0 1 0 0 0 1
		 | b11010010 => byte 1 1 0 1 0 0 1 0
		 | b11010011 => byte 1 1 0 1 0 0 1 1
		 | b11010100 => byte 1 1 0 1 0 1 0 0
		 | b11010101 => byte 1 1 0 1 0 1 0 1
		 | b11010110 => byte 1 1 0 1 0 1 1 0
		 | b11010111 => byte 1 1 0 1 0 1 1 1
		 | b11011000 => byte 1 1 0 1 1 0 0 0
		 | b11011001 => byte 1 1 0 1 1 0 0 1
		 | b11011010 => byte 1 1 0 1 1 0 1 0
		 | b11011011 => byte 1 1 0 1 1 0 1 1
		 | b11011100 => byte 1 1 0 1 1 1 0 0
		 | b11011101 => byte 1 1 0 1 1 1 0 1
		 | b11011110 => byte 1 1 0 1 1 1 1 0
		 | b11011111 => byte 1 1 0 1 1 1 1 1
		 | b11100000 => byte 1 1 1 0 0 0 0 0
		 | b11100001 => byte 1 1 1 0 0 0 0 1
		 | b11100010 => byte 1 1 1 0 0 0 1 0
		 | b11100011 => byte 1 1 1 0 0 0 1 1
		 | b11100100 => byte 1 1 1 0 0 1 0 0
		 | b11100101 => byte 1 1 1 0 0 1 0 1
		 | b11100110 => byte 1 1 1 0 0 1 1 0
		 | b11100111 => byte 1 1 1 0 0 1 1 1
		 | b11101000 => byte 1 1 1 0 1 0 0 0
		 | b11101001 => byte 1 1 1 0 1 0 0 1
		 | b11101010 => byte 1 1 1 0 1 0 1 0
		 | b11101011 => byte 1 1 1 0 1 0 1 1
		 | b11101100 => byte 1 1 1 0 1 1 0 0
		 | b11101101 => byte 1 1 1 0 1 1 0 1
		 | b11101110 => byte 1 1 1 0 1 1 1 0
		 | b11101111 => byte 1 1 1 0 1 1 1 1
		 | b11110000 => byte 1 1 1 1 0 0 0 0
		 | b11110001 => byte 1 1 1 1 0 0 0 1
		 | b11110010 => byte 1 1 1 1 0 0 1 0
		 | b11110011 => byte 1 1 1 1 0 0 1 1
		 | b11110100 => byte 1 1 1 1 0 1 0 0
		 | b11110101 => byte 1 1 1 1 0 1 0 1
		 | b11110110 => byte 1 1 1 1 0 1 1 0
		 | b11110111 => byte 1 1 1 1 0 1 1 1
		 | b11111000 => byte 1 1 1 1 1 0 0 0
		 | b11111001 => byte 1 1 1 1 1 0 0 1
		 | b11111010 => byte 1 1 1 1 1 0 1 0
		 | b11111011 => byte 1 1 1 1 1 0 1 1
		 | b11111100 => byte 1 1 1 1 1 1 0 0
		 | b11111101 => byte 1 1 1 1 1 1 0 1
		 | b11111110 => byte 1 1 1 1 1 1 1 0
		 | b11111111 => byte 1 1 1 1 1 1 1 1
     end.
Coercion bin_to_byte : bytebin >-> Byte.

Inductive bytehex :=
| x00
| x01
| x02
| x03
| x04
| x05
| x06
| x07
| x08
| x09
| x0A
| x0B
| x0C
| x0D
| x0E
| x0F
| x10
| x11
| x12
| x13
| x14
| x15
| x16
| x17
| x18
| x19
| x1A
| x1B
| x1C
| x1D
| x1E
| x1F
| x20
| x21
| x22
| x23
| x24
| x25
| x26
| x27
| x28
| x29
| x2A
| x2B
| x2C
| x2D
| x2E
| x2F
| x30
| x31
| x32
| x33
| x34
| x35
| x36
| x37
| x38
| x39
| x3A
| x3B
| x3C
| x3D
| x3E
| x3F
| x40
| x41
| x42
| x43
| x44
| x45
| x46
| x47
| x48
| x49
| x4A
| x4B
| x4C
| x4D
| x4E
| x4F
| x50
| x51
| x52
| x53
| x54
| x55
| x56
| x57
| x58
| x59
| x5A
| x5B
| x5C
| x5D
| x5E
| x5F
| x60
| x61
| x62
| x63
| x64
| x65
| x66
| x67
| x68
| x69
| x6A
| x6B
| x6C
| x6D
| x6E
| x6F
| x70
| x71
| x72
| x73
| x74
| x75
| x76
| x77
| x78
| x79
| x7A
| x7B
| x7C
| x7D
| x7E
| x7F
| x80
| x81
| x82
| x83
| x84
| x85
| x86
| x87
| x88
| x89
| x8A
| x8B
| x8C
| x8D
| x8E
| x8F
| x90
| x91
| x92
| x93
| x94
| x95
| x96
| x97
| x98
| x99
| x9A
| x9B
| x9C
| x9D
| x9E
| x9F
| xA0
| xA1
| xA2
| xA3
| xA4
| xA5
| xA6
| xA7
| xA8
| xA9
| xAA
| xAB
| xAC
| xAD
| xAE
| xAF
| xB0
| xB1
| xB2
| xB3
| xB4
| xB5
| xB6
| xB7
| xB8
| xB9
| xBA
| xBB
| xBC
| xBD
| xBE
| xBF
| xC0
| xC1
| xC2
| xC3
| xC4
| xC5
| xC6
| xC7
| xC8
| xC9
| xCA
| xCB
| xCC
| xCD
| xCE
| xCF
| xD0
| xD1
| xD2
| xD3
| xD4
| xD5
| xD6
| xD7
| xD8
| xD9
| xDA
| xDB
| xDC
| xDD
| xDE
| xDF
| xE0
| xE1
| xE2
| xE3
| xE4
| xE5
| xE6
| xE7
| xE8
| xE9
| xEA
| xEB
| xEC
| xED
| xEE
| xEF
| xF0
| xF1
| xF2
| xF3
| xF4
| xF5
| xF6
| xF7
| xF8
| xF9
| xFA
| xFB
| xFC
| xFD
| xFE
| xFF
.

Definition hex_to_byte (b : bytehex) : Byte :=
		match b with
		 | x00 => byte 0 0 0 0 0 0 0 0
		 | x01 => byte 0 0 0 0 0 0 0 1
		 | x02 => byte 0 0 0 0 0 0 1 0
		 | x03 => byte 0 0 0 0 0 0 1 1
		 | x04 => byte 0 0 0 0 0 1 0 0
		 | x05 => byte 0 0 0 0 0 1 0 1
		 | x06 => byte 0 0 0 0 0 1 1 0
		 | x07 => byte 0 0 0 0 0 1 1 1
		 | x08 => byte 0 0 0 0 1 0 0 0
		 | x09 => byte 0 0 0 0 1 0 0 1
		 | x0A => byte 0 0 0 0 1 0 1 0
		 | x0B => byte 0 0 0 0 1 0 1 1
		 | x0C => byte 0 0 0 0 1 1 0 0
		 | x0D => byte 0 0 0 0 1 1 0 1
		 | x0E => byte 0 0 0 0 1 1 1 0
		 | x0F => byte 0 0 0 0 1 1 1 1
		 | x10 => byte 0 0 0 1 0 0 0 0
		 | x11 => byte 0 0 0 1 0 0 0 1
		 | x12 => byte 0 0 0 1 0 0 1 0
		 | x13 => byte 0 0 0 1 0 0 1 1
		 | x14 => byte 0 0 0 1 0 1 0 0
		 | x15 => byte 0 0 0 1 0 1 0 1
		 | x16 => byte 0 0 0 1 0 1 1 0
		 | x17 => byte 0 0 0 1 0 1 1 1
		 | x18 => byte 0 0 0 1 1 0 0 0
		 | x19 => byte 0 0 0 1 1 0 0 1
		 | x1A => byte 0 0 0 1 1 0 1 0
		 | x1B => byte 0 0 0 1 1 0 1 1
		 | x1C => byte 0 0 0 1 1 1 0 0
		 | x1D => byte 0 0 0 1 1 1 0 1
		 | x1E => byte 0 0 0 1 1 1 1 0
		 | x1F => byte 0 0 0 1 1 1 1 1
		 | x20 => byte 0 0 1 0 0 0 0 0
		 | x21 => byte 0 0 1 0 0 0 0 1
		 | x22 => byte 0 0 1 0 0 0 1 0
		 | x23 => byte 0 0 1 0 0 0 1 1
		 | x24 => byte 0 0 1 0 0 1 0 0
		 | x25 => byte 0 0 1 0 0 1 0 1
		 | x26 => byte 0 0 1 0 0 1 1 0
		 | x27 => byte 0 0 1 0 0 1 1 1
		 | x28 => byte 0 0 1 0 1 0 0 0
		 | x29 => byte 0 0 1 0 1 0 0 1
		 | x2A => byte 0 0 1 0 1 0 1 0
		 | x2B => byte 0 0 1 0 1 0 1 1
		 | x2C => byte 0 0 1 0 1 1 0 0
		 | x2D => byte 0 0 1 0 1 1 0 1
		 | x2E => byte 0 0 1 0 1 1 1 0
		 | x2F => byte 0 0 1 0 1 1 1 1
		 | x30 => byte 0 0 1 1 0 0 0 0
		 | x31 => byte 0 0 1 1 0 0 0 1
		 | x32 => byte 0 0 1 1 0 0 1 0
		 | x33 => byte 0 0 1 1 0 0 1 1
		 | x34 => byte 0 0 1 1 0 1 0 0
		 | x35 => byte 0 0 1 1 0 1 0 1
		 | x36 => byte 0 0 1 1 0 1 1 0
		 | x37 => byte 0 0 1 1 0 1 1 1
		 | x38 => byte 0 0 1 1 1 0 0 0
		 | x39 => byte 0 0 1 1 1 0 0 1
		 | x3A => byte 0 0 1 1 1 0 1 0
		 | x3B => byte 0 0 1 1 1 0 1 1
		 | x3C => byte 0 0 1 1 1 1 0 0
		 | x3D => byte 0 0 1 1 1 1 0 1
		 | x3E => byte 0 0 1 1 1 1 1 0
		 | x3F => byte 0 0 1 1 1 1 1 1
		 | x40 => byte 0 1 0 0 0 0 0 0
		 | x41 => byte 0 1 0 0 0 0 0 1
		 | x42 => byte 0 1 0 0 0 0 1 0
		 | x43 => byte 0 1 0 0 0 0 1 1
		 | x44 => byte 0 1 0 0 0 1 0 0
		 | x45 => byte 0 1 0 0 0 1 0 1
		 | x46 => byte 0 1 0 0 0 1 1 0
		 | x47 => byte 0 1 0 0 0 1 1 1
		 | x48 => byte 0 1 0 0 1 0 0 0
		 | x49 => byte 0 1 0 0 1 0 0 1
		 | x4A => byte 0 1 0 0 1 0 1 0
		 | x4B => byte 0 1 0 0 1 0 1 1
		 | x4C => byte 0 1 0 0 1 1 0 0
		 | x4D => byte 0 1 0 0 1 1 0 1
		 | x4E => byte 0 1 0 0 1 1 1 0
		 | x4F => byte 0 1 0 0 1 1 1 1
		 | x50 => byte 0 1 0 1 0 0 0 0
		 | x51 => byte 0 1 0 1 0 0 0 1
		 | x52 => byte 0 1 0 1 0 0 1 0
		 | x53 => byte 0 1 0 1 0 0 1 1
		 | x54 => byte 0 1 0 1 0 1 0 0
		 | x55 => byte 0 1 0 1 0 1 0 1
		 | x56 => byte 0 1 0 1 0 1 1 0
		 | x57 => byte 0 1 0 1 0 1 1 1
		 | x58 => byte 0 1 0 1 1 0 0 0
		 | x59 => byte 0 1 0 1 1 0 0 1
		 | x5A => byte 0 1 0 1 1 0 1 0
		 | x5B => byte 0 1 0 1 1 0 1 1
		 | x5C => byte 0 1 0 1 1 1 0 0
		 | x5D => byte 0 1 0 1 1 1 0 1
		 | x5E => byte 0 1 0 1 1 1 1 0
		 | x5F => byte 0 1 0 1 1 1 1 1
		 | x60 => byte 0 1 1 0 0 0 0 0
		 | x61 => byte 0 1 1 0 0 0 0 1
		 | x62 => byte 0 1 1 0 0 0 1 0
		 | x63 => byte 0 1 1 0 0 0 1 1
		 | x64 => byte 0 1 1 0 0 1 0 0
		 | x65 => byte 0 1 1 0 0 1 0 1
		 | x66 => byte 0 1 1 0 0 1 1 0
		 | x67 => byte 0 1 1 0 0 1 1 1
		 | x68 => byte 0 1 1 0 1 0 0 0
		 | x69 => byte 0 1 1 0 1 0 0 1
		 | x6A => byte 0 1 1 0 1 0 1 0
		 | x6B => byte 0 1 1 0 1 0 1 1
		 | x6C => byte 0 1 1 0 1 1 0 0
		 | x6D => byte 0 1 1 0 1 1 0 1
		 | x6E => byte 0 1 1 0 1 1 1 0
		 | x6F => byte 0 1 1 0 1 1 1 1
		 | x70 => byte 0 1 1 1 0 0 0 0
		 | x71 => byte 0 1 1 1 0 0 0 1
		 | x72 => byte 0 1 1 1 0 0 1 0
		 | x73 => byte 0 1 1 1 0 0 1 1
		 | x74 => byte 0 1 1 1 0 1 0 0
		 | x75 => byte 0 1 1 1 0 1 0 1
		 | x76 => byte 0 1 1 1 0 1 1 0
		 | x77 => byte 0 1 1 1 0 1 1 1
		 | x78 => byte 0 1 1 1 1 0 0 0
		 | x79 => byte 0 1 1 1 1 0 0 1
		 | x7A => byte 0 1 1 1 1 0 1 0
		 | x7B => byte 0 1 1 1 1 0 1 1
		 | x7C => byte 0 1 1 1 1 1 0 0
		 | x7D => byte 0 1 1 1 1 1 0 1
		 | x7E => byte 0 1 1 1 1 1 1 0
		 | x7F => byte 0 1 1 1 1 1 1 1
		 | x80 => byte 1 0 0 0 0 0 0 0
		 | x81 => byte 1 0 0 0 0 0 0 1
		 | x82 => byte 1 0 0 0 0 0 1 0
		 | x83 => byte 1 0 0 0 0 0 1 1
		 | x84 => byte 1 0 0 0 0 1 0 0
		 | x85 => byte 1 0 0 0 0 1 0 1
		 | x86 => byte 1 0 0 0 0 1 1 0
		 | x87 => byte 1 0 0 0 0 1 1 1
		 | x88 => byte 1 0 0 0 1 0 0 0
		 | x89 => byte 1 0 0 0 1 0 0 1
		 | x8A => byte 1 0 0 0 1 0 1 0
		 | x8B => byte 1 0 0 0 1 0 1 1
		 | x8C => byte 1 0 0 0 1 1 0 0
		 | x8D => byte 1 0 0 0 1 1 0 1
		 | x8E => byte 1 0 0 0 1 1 1 0
		 | x8F => byte 1 0 0 0 1 1 1 1
		 | x90 => byte 1 0 0 1 0 0 0 0
		 | x91 => byte 1 0 0 1 0 0 0 1
		 | x92 => byte 1 0 0 1 0 0 1 0
		 | x93 => byte 1 0 0 1 0 0 1 1
		 | x94 => byte 1 0 0 1 0 1 0 0
		 | x95 => byte 1 0 0 1 0 1 0 1
		 | x96 => byte 1 0 0 1 0 1 1 0
		 | x97 => byte 1 0 0 1 0 1 1 1
		 | x98 => byte 1 0 0 1 1 0 0 0
		 | x99 => byte 1 0 0 1 1 0 0 1
		 | x9A => byte 1 0 0 1 1 0 1 0
		 | x9B => byte 1 0 0 1 1 0 1 1
		 | x9C => byte 1 0 0 1 1 1 0 0
		 | x9D => byte 1 0 0 1 1 1 0 1
		 | x9E => byte 1 0 0 1 1 1 1 0
		 | x9F => byte 1 0 0 1 1 1 1 1
		 | xA0 => byte 1 0 1 0 0 0 0 0
		 | xA1 => byte 1 0 1 0 0 0 0 1
		 | xA2 => byte 1 0 1 0 0 0 1 0
		 | xA3 => byte 1 0 1 0 0 0 1 1
		 | xA4 => byte 1 0 1 0 0 1 0 0
		 | xA5 => byte 1 0 1 0 0 1 0 1
		 | xA6 => byte 1 0 1 0 0 1 1 0
		 | xA7 => byte 1 0 1 0 0 1 1 1
		 | xA8 => byte 1 0 1 0 1 0 0 0
		 | xA9 => byte 1 0 1 0 1 0 0 1
		 | xAA => byte 1 0 1 0 1 0 1 0
		 | xAB => byte 1 0 1 0 1 0 1 1
		 | xAC => byte 1 0 1 0 1 1 0 0
		 | xAD => byte 1 0 1 0 1 1 0 1
		 | xAE => byte 1 0 1 0 1 1 1 0
		 | xAF => byte 1 0 1 0 1 1 1 1
		 | xB0 => byte 1 0 1 1 0 0 0 0
		 | xB1 => byte 1 0 1 1 0 0 0 1
		 | xB2 => byte 1 0 1 1 0 0 1 0
		 | xB3 => byte 1 0 1 1 0 0 1 1
		 | xB4 => byte 1 0 1 1 0 1 0 0
		 | xB5 => byte 1 0 1 1 0 1 0 1
		 | xB6 => byte 1 0 1 1 0 1 1 0
		 | xB7 => byte 1 0 1 1 0 1 1 1
		 | xB8 => byte 1 0 1 1 1 0 0 0
		 | xB9 => byte 1 0 1 1 1 0 0 1
		 | xBA => byte 1 0 1 1 1 0 1 0
		 | xBB => byte 1 0 1 1 1 0 1 1
		 | xBC => byte 1 0 1 1 1 1 0 0
		 | xBD => byte 1 0 1 1 1 1 0 1
		 | xBE => byte 1 0 1 1 1 1 1 0
		 | xBF => byte 1 0 1 1 1 1 1 1
		 | xC0 => byte 1 1 0 0 0 0 0 0
		 | xC1 => byte 1 1 0 0 0 0 0 1
		 | xC2 => byte 1 1 0 0 0 0 1 0
		 | xC3 => byte 1 1 0 0 0 0 1 1
		 | xC4 => byte 1 1 0 0 0 1 0 0
		 | xC5 => byte 1 1 0 0 0 1 0 1
		 | xC6 => byte 1 1 0 0 0 1 1 0
		 | xC7 => byte 1 1 0 0 0 1 1 1
		 | xC8 => byte 1 1 0 0 1 0 0 0
		 | xC9 => byte 1 1 0 0 1 0 0 1
		 | xCA => byte 1 1 0 0 1 0 1 0
		 | xCB => byte 1 1 0 0 1 0 1 1
		 | xCC => byte 1 1 0 0 1 1 0 0
		 | xCD => byte 1 1 0 0 1 1 0 1
		 | xCE => byte 1 1 0 0 1 1 1 0
		 | xCF => byte 1 1 0 0 1 1 1 1
		 | xD0 => byte 1 1 0 1 0 0 0 0
		 | xD1 => byte 1 1 0 1 0 0 0 1
		 | xD2 => byte 1 1 0 1 0 0 1 0
		 | xD3 => byte 1 1 0 1 0 0 1 1
		 | xD4 => byte 1 1 0 1 0 1 0 0
		 | xD5 => byte 1 1 0 1 0 1 0 1
		 | xD6 => byte 1 1 0 1 0 1 1 0
		 | xD7 => byte 1 1 0 1 0 1 1 1
		 | xD8 => byte 1 1 0 1 1 0 0 0
		 | xD9 => byte 1 1 0 1 1 0 0 1
		 | xDA => byte 1 1 0 1 1 0 1 0
		 | xDB => byte 1 1 0 1 1 0 1 1
		 | xDC => byte 1 1 0 1 1 1 0 0
		 | xDD => byte 1 1 0 1 1 1 0 1
		 | xDE => byte 1 1 0 1 1 1 1 0
		 | xDF => byte 1 1 0 1 1 1 1 1
		 | xE0 => byte 1 1 1 0 0 0 0 0
		 | xE1 => byte 1 1 1 0 0 0 0 1
		 | xE2 => byte 1 1 1 0 0 0 1 0
		 | xE3 => byte 1 1 1 0 0 0 1 1
		 | xE4 => byte 1 1 1 0 0 1 0 0
		 | xE5 => byte 1 1 1 0 0 1 0 1
		 | xE6 => byte 1 1 1 0 0 1 1 0
		 | xE7 => byte 1 1 1 0 0 1 1 1
		 | xE8 => byte 1 1 1 0 1 0 0 0
		 | xE9 => byte 1 1 1 0 1 0 0 1
		 | xEA => byte 1 1 1 0 1 0 1 0
		 | xEB => byte 1 1 1 0 1 0 1 1
		 | xEC => byte 1 1 1 0 1 1 0 0
		 | xED => byte 1 1 1 0 1 1 0 1
		 | xEE => byte 1 1 1 0 1 1 1 0
		 | xEF => byte 1 1 1 0 1 1 1 1
		 | xF0 => byte 1 1 1 1 0 0 0 0
		 | xF1 => byte 1 1 1 1 0 0 0 1
		 | xF2 => byte 1 1 1 1 0 0 1 0
		 | xF3 => byte 1 1 1 1 0 0 1 1
		 | xF4 => byte 1 1 1 1 0 1 0 0
		 | xF5 => byte 1 1 1 1 0 1 0 1
		 | xF6 => byte 1 1 1 1 0 1 1 0
		 | xF7 => byte 1 1 1 1 0 1 1 1
		 | xF8 => byte 1 1 1 1 1 0 0 0
		 | xF9 => byte 1 1 1 1 1 0 0 1
		 | xFA => byte 1 1 1 1 1 0 1 0
		 | xFB => byte 1 1 1 1 1 0 1 1
		 | xFC => byte 1 1 1 1 1 1 0 0
		 | xFD => byte 1 1 1 1 1 1 0 1
		 | xFE => byte 1 1 1 1 1 1 1 0
		 | xFF => byte 1 1 1 1 1 1 1 1
     end.
Coercion hex_to_byte : bytehex >-> Byte.
Check byte 0 0 0 0 0 0 0 0.

Compute byte_to_nat (hex_to_byte x0F).
Compute byte_to_nat (bin_to_byte b00000101).

Definition n := nat_to_byte 10.
Compute n.
Check Z.
Delimit Scope Z_scope with Z.
Check 1000.
Compute byte_to_nat n.

Check bit 1.

Inductive Word :=
| word : Byte -> Byte -> Word.
Definition word_to_nat (w : Word) : Z :=
		match w with
			word b1 b2 => 256*byte_to_nat b1 + byte_to_nat b2
		end.

Inductive DWord :=
| dword : Word -> Word -> DWord.
Definition dword_to_nat (d : DWord) : Z :=
		match d with
			dword w1 w2 => 65536*word_to_nat w1 + word_to_nat w2
		end.
Compute dword_to_nat (dword (word xFF xFF) (word xFF xFF)).

Definition w := word b00000000 xFF.
Compute w.

Inductive ByteReg := AH|AL | BH|BL | CH|CL | DH|DL.
Inductive WordReg := AX | BX | CX | DX.
Inductive NonSPReg := EAX| EBX | ECX | EDX | ESI | EDI | EBP.
Inductive Reg := nonSPReg (r : NonSPReg) | ESP.
Inductive AnyReg := regToAnyReg (r : Reg) | EIP.


