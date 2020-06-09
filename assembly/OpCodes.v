Require Import Coq.Init.Byte.

Notation EXIT := x00.
Notation NOP := x01.
Notation JUMP := x02.
Notation JUMP_ZERO := x03.
Notation SET_SP := x04.
Notation GET_PC := x05.
Notation GET_SP := x06.
Notation PUSH0 := x07.
Notation PUSH1 := x08.
Notation PUSH2 := x09.
Notation PUSH4 := x0a.
Notation PUSH8 := x0b.
Notation SIGX1 := x0c.
Notation SIGX2 := x0d.
Notation SIGX4 := x0e.
Notation LOAD1 := x10.
Notation LOAD2 := x11.
Notation LOAD4 := x12.
Notation LOAD8 := x13.
Notation STORE1 := x14.
Notation STORE2 := x15.
Notation STORE4 := x16.
Notation STORE8 := x17.
Notation ADD := x20.
Notation MULT := x21.
Notation DIV := x22.
Notation REM := x23.
Notation LT := x24.
Notation AND := x28.
Notation OR := x29.
Notation NOT := x2a.
Notation XOR := x2b.
Notation POW2 := x2c.

Notation READ_FRAME := xff.
Notation READ_PIXEL := xfe.
Notation NEW_FRAME := xfd.
Notation SET_PIXEL := xfc.
Notation ADD_SAMPLE := xfb.
Notation PUT_CHAR := xfa.
Notation PUT_BYTE := xf9.
