Require Import Utf8.

Require Import Assembly.Bits.
Require Assembly.OpCodes.

Notation EXIT := (toB8 OpCodes.EXIT).
Notation NOP := (toB8 OpCodes.NOP).
Notation JUMP := (toB8 OpCodes.JUMP).
Notation JUMP_ZERO := (toB8 OpCodes.JUMP_ZERO).
Notation SET_SP := (toB8 OpCodes.SET_SP).
Notation GET_PC := (toB8 OpCodes.GET_PC).
Notation GET_SP := (toB8 OpCodes.GET_SP).
Notation PUSH0 := (toB8 OpCodes.PUSH0).
Notation PUSH1 := (toB8 OpCodes.PUSH1).
Notation PUSH2 := (toB8 OpCodes.PUSH2).
Notation PUSH4 := (toB8 OpCodes.PUSH4).
Notation PUSH8 := (toB8 OpCodes.PUSH8).
Notation SIGX1 := (toB8 OpCodes.SIGX1).
Notation SIGX2 := (toB8 OpCodes.SIGX2).
Notation SIGX4 := (toB8 OpCodes.SIGX4).
Notation LOAD1 := (toB8 OpCodes.LOAD1).
Notation LOAD2 := (toB8 OpCodes.LOAD2).
Notation LOAD4 := (toB8 OpCodes.LOAD4).
Notation LOAD8 := (toB8 OpCodes.LOAD8).
Notation STORE1 := (toB8 OpCodes.STORE1).
Notation STORE2 := (toB8 OpCodes.STORE2).
Notation STORE4 := (toB8 OpCodes.STORE4).
Notation STORE8 := (toB8 OpCodes.STORE8).
Notation ADD := (toB8 OpCodes.ADD).
Notation MULT := (toB8 OpCodes.MULT).
Notation DIV := (toB8 OpCodes.DIV).
Notation REM := (toB8 OpCodes.REM).
Notation LT := (toB8 OpCodes.LT).
Notation AND := (toB8 OpCodes.AND).
Notation OR := (toB8 OpCodes.OR).
Notation NOT := (toB8 OpCodes.NOT).
Notation XOR := (toB8 OpCodes.XOR).
Notation POW2 := (toB8 OpCodes.POW2).

Notation READ_FRAME := (toB8 OpCodes.READ_FRAME).
Notation READ_PIXEL := (toB8 OpCodes.READ_PIXEL).
Notation NEW_FRAME := (toB8 OpCodes.NEW_FRAME).
Notation SET_PIXEL := (toB8 OpCodes.SET_PIXEL).
Notation ADD_SAMPLE := (toB8 OpCodes.ADD_SAMPLE).
Notation PUT_CHAR := (toB8 OpCodes.PUT_CHAR).
Notation PUT_BYTE := (toB8 OpCodes.PUT_BYTE).
