#ifdef ARCH_I686
    .text
    .global egalito_hook_function_entry
egalito_hook_function_entry:
    mov    %fs:-0x10, %eax
    cmp    $0x0, %eax
    jne     1f
    push    %ebx
//    movq    $0x1, %fs:-0x10
	//    mov     0x4(%esp), %edi
    push  0x4(%esp)
    mov     egalito_hook_function_entry_hook@got, %eax //pcrel(%eip), %eax
    call   *(%eax)
	//    mov     $0x0, %fs:-0x10
    add    0x4, %esp
    pop     %ebx
1:
    ret
    .type egalito_hook_function_entry, STT_FUNC
    .size egalito_hook_function_entry, .-egalito_hook_function_entry


    .global egalito_hook_function_exit
egalito_hook_function_exit:
    mov    %fs:-0x10, %eax
    cmp    $0x0, %eax
    jne     1f
    push    %ebx
    //movq    $0x1, %fs:-0x10
    push   0x4(%esp)
    mov     egalito_hook_function_exit_hook@got, %eax //@gotpcrel(%eip), %eax
    call   *(%eax)
	//movq    $0x0, %fs:-0x10
    add     0x4, %esp
    pop     %ebx
1:
    ret
    .type egalito_hook_function_exit, STT_FUNC
    .size egalito_hook_function_exit, .-egalito_hook_function_exit

    .global egalito_hook_instruction
egalito_hook_instruction:
    //mov     %fs:-0x10, %eax
    cmp    $0x0, %eax
    jne     1f
    push    %ebx
    //movq    $0x1, %fs:-0x10
    //mov     0x8(%esp), %edi
    push 0x4(%esp)
    mov     egalito_hook_instruction_hook@got, %eax //@gotpcrel(%eip), %eax
    call   *(%eax)
    add   0x4, %esp
    //movq    $0x0, %fs:-0x10
    pop     %ebx
1:
    ret
    .type egalito_hook_instruction, STT_FUNC
    .size egalito_hook_instruction, .-egalito_hook_instruction

egalito_hook_after_clone_syscall:
    test    %eax, %eax
    jnz     1f

    //jmp     .
    push   %eax
    mov     egalito_jit_gs_setup_thread@got, %eax //@gotpcrel(%eip), %eax
    call   *%eax
    pop    %eax
1:
    ret
    .type egalito_hook_after_clone_syscall, STT_FUNC
    .size egalito_hook_after_clone_syscall, .-egalito_hook_after_clone_syscall

//
// begin .bss section
//
    .bss
    .align 8

    .global egalito_hook_function_entry_hook
    .weak egalito_hook_function_entry_hook
egalito_hook_function_entry_hook:
    .skip 8
    .type egalito_hook_function_entry_hook, STT_OBJECT
    .size egalito_hook_function_entry_hook, .-egalito_hook_function_entry_hook

    .global egalito_hook_function_exit_hook
    .weak egalito_hook_function_exit_hook
egalito_hook_function_exit_hook:
    .skip 8
    .type egalito_hook_function_exit_hook, STT_OBJECT
    .size egalito_hook_function_exit_hook, .-egalito_hook_function_exit_hook

    .global egalito_hook_instruction_hook
    .weak egalito_hook_instruction_hook
egalito_hook_instruction_hook:
    .skip 8
    .type egalito_hook_instruction_hook, STT_OBJECT
    .size egalito_hook_instruction_hook, .-egalito_hook_instruction_hook
#endif
