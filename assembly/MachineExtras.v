From Assembly Require Export Machine MonExtras.
From RecordUpdate Require Import RecordSet.

(** The purpose of this file is to prove the (rather trivial) fact that
the initial error state monad over the obvious record type does indeed
satisfy the constraints in [MachineParams1].*)

Record State :=
mkState {
  state_memory: Memory;
  state_pc: Addr;
  state_sp: Addr;
  state_inp: N;
  state_image: Image (option OutputColor);
  state_bytes: list Byte;
  state_chars: list Char;
  state_sound: Sound;
  state_log: list OutputFrame;
}.
Instance etaState : Settable _ :=
  settable! mkState <state_memory;
                     state_pc;
                     state_sp;
                     state_inp;
                     state_image;
                     state_bytes;
                     state_chars;
                     state_sound;
                     state_log>.

Local Ltac crush :=
  let s := fresh in try split; intro s; intros; destruct s; reflexivity.

Local Ltac derive_lens f :=
  refine {|
      proj := f;
      update s m := set f (fun _ => m) s;
  |}; crush.

Definition MEM : Lens State Memory. derive_lens state_memory. Defined.
Definition PC : Lens State Addr. derive_lens state_pc. Defined.
Definition SP : Lens State Addr. derive_lens state_sp. Defined.
Definition INP : Lens State N. derive_lens state_inp. Defined.
Definition OUT_CHARS : Lens State (list Char). derive_lens state_chars. Defined.
Definition OUT_BYTES : Lens State (list Byte). derive_lens state_bytes. Defined.
Definition OUT_SOUND : Lens State Sound. derive_lens state_sound. Defined.
Definition OUT_IMAGE : Lens State (Image (option OutputColor)). derive_lens state_image. Defined.
Definition LOG : Lens State (list OutputFrame). derive_lens state_log. Defined.

Instance independent_MEM_IMAGE: Independent MEM OUT_IMAGE. crush. Defined.
Instance independent_MEM_BYTES: Independent MEM OUT_BYTES. crush. Defined.
Instance independent_MEM_CHARS: Independent MEM OUT_CHARS. crush. Defined.
Instance independent_MEM_SOUND: Independent MEM OUT_SOUND. crush. Defined.
Instance independent_MEM_LOG:   Independent MEM LOG. crush. Defined.
Instance independent_MEM_INP:   Independent MEM INP. crush. Defined.
Instance independent_MEM_PC:    Independent MEM PC. crush. Defined.
Instance independent_MEM_SP:    Independent MEM SP. crush. Defined.

Instance independent_IMAGE_BYTES: Independent OUT_IMAGE OUT_BYTES. crush. Defined.
Instance independent_IMAGE_CHARS: Independent OUT_IMAGE OUT_CHARS. crush. Defined.
Instance independent_IMAGE_SOUND: Independent OUT_IMAGE OUT_SOUND. crush. Defined.
Instance independent_IMAGE_LOG:   Independent OUT_IMAGE LOG. crush. Defined.
Instance independent_IMAGE_INP:   Independent OUT_IMAGE INP. crush. Defined.
Instance independent_IMAGE_PC:    Independent OUT_IMAGE PC. crush. Defined.
Instance independent_IMAGE_SP:    Independent OUT_IMAGE SP. crush. Defined.

Instance independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS. crush. Defined.
Instance independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND. crush. Defined.
Instance independent_BYTES_LOG:   Independent OUT_BYTES LOG. crush. Defined.
Instance independent_BYTES_INP:   Independent OUT_BYTES INP. crush. Defined.
Instance independent_BYTES_PC:    Independent OUT_BYTES PC. crush. Defined.
Instance independent_BYTES_SP:    Independent OUT_BYTES SP. crush. Defined.

Instance independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND. crush. Defined.
Instance independent_CHARS_LOG:   Independent OUT_CHARS LOG. crush. Defined.
Instance independent_CHARS_INP:   Independent OUT_CHARS INP. crush. Defined.
Instance independent_CHARS_PC:    Independent OUT_CHARS PC. crush. Defined.
Instance independent_CHARS_SP:    Independent OUT_CHARS SP. crush. Defined.

Instance independent_SOUND_LOG: Independent OUT_SOUND LOG. crush. Defined.
Instance independent_SOUND_INP: Independent OUT_SOUND INP. crush. Defined.
Instance independent_SOUND_PC:  Independent OUT_SOUND PC. crush. Defined.
Instance independent_SOUND_SP:  Independent OUT_SOUND SP. crush. Defined.

Instance independent_LOG_INP: Independent LOG INP. crush. Defined.
Instance independent_LOG_PC:  Independent LOG PC. crush. Defined.
Instance independent_LOG_SP:  Independent LOG SP. crush. Defined.

Instance independent_INP_PC: Independent INP PC. crush. Defined.
Instance independent_INP_SP: Independent INP SP. crush. Defined.

Instance independent_PC_SP: Independent PC SP. crush. Defined.

Instance concreteParams1 : MachineParams1 :=
{
    State := State;

    MEM := MEM;
    PC := PC;
    SP := SP;

    INP := INP;

    OUT_CHARS  := OUT_CHARS ;
    OUT_BYTES  := OUT_BYTES ;
    OUT_SOUND  := OUT_SOUND ;
    OUT_IMAGE  := OUT_IMAGE ;

    LOG := LOG;

    independent_MEM_IMAGE := independent_MEM_IMAGE;
    independent_MEM_BYTES := independent_MEM_BYTES;
    independent_MEM_CHARS := independent_MEM_CHARS;
    independent_MEM_SOUND := independent_MEM_SOUND;
    independent_MEM_LOG := independent_MEM_LOG;
    independent_MEM_INP := independent_MEM_INP;
    independent_MEM_PC := independent_MEM_PC;
    independent_MEM_SP := independent_MEM_SP;

    independent_IMAGE_BYTES := independent_IMAGE_BYTES;
    independent_IMAGE_CHARS := independent_IMAGE_CHARS;
    independent_IMAGE_SOUND := independent_IMAGE_SOUND;
    independent_IMAGE_LOG := independent_IMAGE_LOG;
    independent_IMAGE_INP := independent_IMAGE_INP;
    independent_IMAGE_PC := independent_IMAGE_PC;
    independent_IMAGE_SP := independent_IMAGE_SP;

    independent_BYTES_CHARS := independent_BYTES_CHARS;
    independent_BYTES_SOUND := independent_BYTES_SOUND;
    independent_BYTES_LOG := independent_BYTES_LOG;
    independent_BYTES_INP := independent_BYTES_INP;
    independent_BYTES_PC := independent_BYTES_PC;
    independent_BYTES_SP := independent_BYTES_SP;

    independent_CHARS_SOUND := independent_CHARS_SOUND;
    independent_CHARS_LOG := independent_CHARS_LOG;
    independent_CHARS_INP := independent_CHARS_INP;
    independent_CHARS_PC := independent_CHARS_PC;
    independent_CHARS_SP := independent_CHARS_SP;

    independent_SOUND_LOG := independent_SOUND_LOG;
    independent_SOUND_INP := independent_SOUND_INP;
    independent_SOUND_PC := independent_SOUND_PC;
    independent_SOUND_SP := independent_SOUND_SP;

    independent_LOG_INP := independent_LOG_INP;
    independent_LOG_PC := independent_LOG_PC;
    independent_LOG_SP := independent_LOG_SP;

    independent_INP_PC := independent_INP_PC;
    independent_INP_SP := independent_INP_SP;

    independent_PC_SP := independent_PC_SP;
}.

Instance concreteParams2 : MachineParams2 :=
{
    M := EST State;
    H_mon := est_smonad State;
}.
