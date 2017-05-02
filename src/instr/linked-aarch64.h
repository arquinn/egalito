#ifndef EGALITO_INSTR_LINKED_AARCH64_H
#define EGALITO_INSTR_LINKED_AARCH64_H

#include "semantic.h"
#include "isolated.h"
#include "chunk/chunkfwd.h"

// Defines LinkedInstruction and ControlFlowInstruction for aarch64.

#if defined(ARCH_AARCH64)
class LinkedInstruction : public LinkDecorator<DisassembledInstruction> {
public:
    enum Mode {
        AARCH64_IM_ADRP = 0,
        AARCH64_IM_ADDIMM,
        AARCH64_IM_LDR,
        AARCH64_IM_BL,
        AARCH64_IM_B,
        AARCH64_IM_BCOND,
        AARCH64_IM_CBZ,
        AARCH64_IM_CBNZ,
        AARCH64_IM_TBZ,
        AARCH64_IM_TBNZ,
        AARCH64_IM_MAX
    };

private:
    struct AARCH64_modeInfo_t {
        uint32_t fixedMask;
        uint32_t (*makeImm)(address_t, address_t);
        int immediateIndex;
    };

    const static AARCH64_modeInfo_t AARCH64_ImInfo[AARCH64_IM_MAX];

    Instruction *source;
    const AARCH64_modeInfo_t *modeInfo;

public:
    LinkedInstruction(Instruction *source,
                      const Assembly &assembly);

    void writeTo(char *target, bool useDisp);
    void writeTo(std::string &target, bool useDisp);

    void regenerateAssembly();

    static LinkedInstruction *makeLinked(Module *module,
        Instruction *instruction, Assembly *assembly);

    Instruction *getSource() const { return source; }
    std::string getMnemonic() { return getAssembly()->getMnemonic(); }

    const AARCH64_modeInfo_t *getModeInfo() const { return modeInfo; }
    uint32_t getOriginalOffset() const;

    uint32_t rebuild();

    virtual void accept(InstructionVisitor *visitor) { visitor->visit(this); }
private:
    static Mode getMode(const Assembly &assembly);
    static address_t makeTargetAddress(Instruction *instruction,
        Assembly *assembly, int regIndex);
};

class ControlFlowInstruction : public LinkedInstruction {
public:
    using LinkedInstruction::LinkedInstruction;

    virtual void accept(InstructionVisitor *visitor) { visitor->visit(this); }
};
#endif

#endif
