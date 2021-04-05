/*
   american fuzzy lop++ - high-performance binary-only instrumentation
   -------------------------------------------------------------------

   Originally written by Andrew Griffiths <agriffiths@google.com> and
                         Michal Zalewski

   TCG instrumentation and block chaining support by Andrea Biondo
                                      <andrea.biondo965@gmail.com>

   QEMU 3.1.1 port, TCG thread-safety, CompareCoverage and NeverZero
   counters by Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2015, 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This code is a shim patched into the separately-distributed source
   code of QEMU 3.1.0. It leverages the built-in QEMU tracing functionality
   to implement AFL-style instrumentation and to take care of the remaining
   parts of the AFL fork server logic.

   The resulting QEMU binary is essentially a standalone instrumentation
   tool; for an example of how to leverage it for other purposes, you can
   have a look at afl-showmap.c.

 */

#include "afl-qemu-common.h"
#include "tcg.h"
#include "tcg-op.h"

static void afl_compcov_log_16(target_ulong cur_loc, target_ulong arg1,
                               target_ulong arg2) {

  register uintptr_t idx = cur_loc;

  if ((arg1 & 0xff00) == (arg2 & 0xff00)) { INC_AFL_AREA(idx); }

}

static void afl_compcov_log_32(target_ulong cur_loc, target_ulong arg1,
                               target_ulong arg2) {

  register uintptr_t idx = cur_loc;

  if ((arg1 & 0xff000000) == (arg2 & 0xff000000)) {

    INC_AFL_AREA(idx + 2);
    if ((arg1 & 0xff0000) == (arg2 & 0xff0000)) {

      INC_AFL_AREA(idx + 1);
      if ((arg1 & 0xff00) == (arg2 & 0xff00)) { INC_AFL_AREA(idx); }

    }

  }

}

static void afl_compcov_log_64(target_ulong cur_loc, target_ulong arg1,
                               target_ulong arg2) {

  register uintptr_t idx = cur_loc;

  if ((arg1 & 0xff00000000000000) == (arg2 & 0xff00000000000000)) {

    INC_AFL_AREA(idx + 6);
    if ((arg1 & 0xff000000000000) == (arg2 & 0xff000000000000)) {

      INC_AFL_AREA(idx + 5);
      if ((arg1 & 0xff0000000000) == (arg2 & 0xff0000000000)) {

        INC_AFL_AREA(idx + 4);
        if ((arg1 & 0xff00000000) == (arg2 & 0xff00000000)) {

          INC_AFL_AREA(idx + 3);
          if ((arg1 & 0xff000000) == (arg2 & 0xff000000)) {

            INC_AFL_AREA(idx + 2);
            if ((arg1 & 0xff0000) == (arg2 & 0xff0000)) {

              INC_AFL_AREA(idx + 1);
              if ((arg1 & 0xff00) == (arg2 & 0xff00)) { INC_AFL_AREA(idx); }

            }

          }

        }

      }

    }

  }

}

static void afl_gen_compcov(target_ulong cur_loc, TCGv_i64 arg1, TCGv_i64 arg2,
                            TCGMemOp ot, int is_imm) {

  void *func;

  if (!afl_compcov_level || cur_loc > afl_end_code || cur_loc < afl_start_code)
    return;

  if (!is_imm && afl_compcov_level < 2) return;

  switch (ot) {

    case MO_64: func = &afl_compcov_log_64; break;
    case MO_32: func = &afl_compcov_log_32; break;
    case MO_16: func = &afl_compcov_log_16; break;
    default: return;

  }

  cur_loc = (cur_loc >> 4) ^ (cur_loc << 8);
  cur_loc &= MAP_SIZE - 7;

  if (cur_loc >= afl_inst_rms) return;

  tcg_gen_afl_compcov_log_call(func, cur_loc, arg1, arg2);

}

/* Routines for debug */
/*
static void log_x86_saved_gpr(void) {

  static const char reg_names[CPU_NB_REGS][4] = {

#ifdef TARGET_X86_64
        [R_EAX] = "rax",
        [R_EBX] = "rbx",
        [R_ECX] = "rcx",
        [R_EDX] = "rdx",
        [R_ESI] = "rsi",
        [R_EDI] = "rdi",
        [R_EBP] = "rbp",
        [R_ESP] = "rsp",
        [8]  = "r8",
        [9]  = "r9",
        [10] = "r10",
        [11] = "r11",
        [12] = "r12",
        [13] = "r13",
        [14] = "r14",
        [15] = "r15",
#else
        [R_EAX] = "eax",
        [R_EBX] = "ebx",
        [R_ECX] = "ecx",
        [R_EDX] = "edx",
        [R_ESI] = "esi",
        [R_EDI] = "edi",
        [R_EBP] = "ebp",
        [R_ESP] = "esp",
#endif

    };

  int i;
  for (i = 0; i < CPU_NB_REGS; ++i) {

    fprintf(stderr, "%s = %lx\n", reg_names[i], persistent_saved_gpr[i]);

  }

}

static void log_x86_sp_content(void) {

  fprintf(stderr, ">> SP = %lx -> %lx\n", persistent_saved_gpr[R_ESP],
*(unsigned long*)persistent_saved_gpr[R_ESP]);

}*/

#define I386_RESTORE_STATE_FOR_PERSISTENT                               \
  do {                                                                  \
                                                                        \
    if (persistent_save_gpr) {                                          \
                                                                        \
      int      i;                                                       \
      TCGv_ptr gpr_sv;                                                  \
                                                                        \
      TCGv_ptr first_pass_ptr = tcg_const_ptr(&persistent_first_pass);  \
      TCGv     first_pass = tcg_temp_local_new();                       \
      TCGv     one = tcg_const_tl(1);                                   \
      tcg_gen_ld8u_tl(first_pass, first_pass_ptr, 0);                   \
                                                                        \
      TCGLabel *lbl_save_gpr = gen_new_label();                         \
      TCGLabel *lbl_finish_restore_gpr = gen_new_label();               \
      tcg_gen_brcond_tl(TCG_COND_EQ, first_pass, one, lbl_save_gpr);    \
                                                                        \
      for (i = 0; i < CPU_NB_REGS; ++i) {                               \
                                                                        \
        gpr_sv = tcg_const_ptr(&persistent_saved_gpr[i]);               \
        tcg_gen_ld_tl(cpu_regs[i], gpr_sv, 0);                          \
                                                                        \
      }                                                                 \
                                                                        \
      tcg_gen_br(lbl_finish_restore_gpr);                               \
                                                                        \
      gen_set_label(lbl_save_gpr);                                      \
                                                                        \
      for (i = 0; i < CPU_NB_REGS; ++i) {                               \
                                                                        \
        gpr_sv = tcg_const_ptr(&persistent_saved_gpr[i]);               \
        tcg_gen_st_tl(cpu_regs[i], gpr_sv, 0);                          \
                                                                        \
      }                                                                 \
                                                                        \
      gen_set_label(lbl_finish_restore_gpr);                            \
      tcg_temp_free(first_pass);                                        \
                                                                        \
    } else if (afl_persistent_ret_addr == 0) {                          \
                                                                        \
      TCGv_ptr stack_off_ptr = tcg_const_ptr(&persistent_stack_offset); \
      TCGv     stack_off = tcg_temp_new();                              \
      tcg_gen_ld_tl(stack_off, stack_off_ptr, 0);                       \
      tcg_gen_sub_tl(cpu_regs[R_ESP], cpu_regs[R_ESP], stack_off);      \
      tcg_temp_free(stack_off);                                         \
                                                                        \
    }                                                                   \
                                                                        \
  } while (0)

#define AFL_QEMU_TARGET_i386_SNIPPET                                          \
  if (is_persistent) {                                                        \
                                                                              \
    if (s->pc == afl_persistent_addr) {                                       \
                                                                              \
      I386_RESTORE_STATE_FOR_PERSISTENT;                                      \
      /*tcg_gen_afl_call0(log_x86_saved_gpr);                                 \
      tcg_gen_afl_call0(log_x86_sp_content);*/                                \
                                                                              \
      if (afl_persistent_ret_addr == 0) {                                     \
                                                                              \
        TCGv_ptr paddr = tcg_const_ptr(afl_persistent_addr);                  \
        tcg_gen_st_tl(paddr, cpu_regs[R_ESP], persisent_retaddr_offset);      \
                                                                              \
      }                                                                       \
      tcg_gen_afl_call0(&afl_persistent_loop);                                \
      /*tcg_gen_afl_call0(log_x86_sp_content);*/                              \
                                                                              \
    } else if (afl_persistent_ret_addr && s->pc == afl_persistent_ret_addr) { \
                                                                              \
      gen_jmp_im(s, afl_persistent_addr);                                     \
      gen_eob(s);                                                             \
                                                                              \
    }                                                                         \
                                                                              \
  }

