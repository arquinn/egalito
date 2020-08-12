#ifdef ARCH_I686
    .text
    .global ifunc_resolver
ifunc_resolver:
    /* there may be some more registers (e.g. XMM) */
    push    %eax
    push    %ecx
    push    %edx
    push    %esi
    push    %edi
    mov     0x40(%esp), %edi
	// call    *ifunc_select@got //pcrel(%eip)
    pop     %edi
    pop     %esi
    pop     %edx
    pop     %ecx
    pop     %eax
    pop     %ebx    # pushed by plt
    jmp    *(%ebx)
    .type ifunc_resolver, STT_FUNC
    .size ifunc_resolver, .-ifunc_resolver
#endif
