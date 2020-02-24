.global _start2
.global egalito_initial_stack
.global egalito_entry

.section .bss
egalito_initial_stack:
    .skip   8
    .type egalito_initial_stack, STT_OBJECT
    .weak egalito_initial_stack
egalito_entry:
    .skip   8
    .type egalito_entry, STT_OBJECT
    .weak egalito_entry

.section .text
/* This has to be called in the target context */
_start2:
    .cfi_startproc
    .cfi_undefined %eip
    push    %ebx                    /* keep alignment */
    call    *egalito_callInit@got //gotpcrel(%eip)
    pop     %ebx

    mov     egalito_initial_stack@got, %eax //pltgotpcrel(%eip), %eax
    mov     (%eax), %esp            /* restore %rsp */
    xor     %edx, %edx  /* clear for now since loader is static */

    mov     egalito_entry@got, %ebx  // pcrel(%eip), %ebx
    jmp     *(%ebx)
    hlt
    .cfi_endproc
    .type _start2, STT_FUNC
    .size _start2, .-_start2

