#include <iostream>
#include <iomanip>
#include <cstring>
#include <cstdio>  // for std::fflush

#include "usage.h"
#include "segmap.h"
#include "elf/auxv.h"
#include "elf/elfmap.h"
#include "elf/elfspace.h"
#include "conductor/conductor.h"
#include "chunk/chunk.h"
#include "chunk/chunklist.h"
#include "chunk/dump.h"
#include "transform/sandbox.h"
#include "transform/generator.h"
#include "break/signals.h"
#include "analysis/controlflow.h"
#include "analysis/jumptable.h"
#include "log/registry.h"
#include "log/log.h"

extern address_t entry;
extern "C" void _start2(void);

void runEgalito(ElfMap *elf);
void setBreakpointsInInterpreter(ElfMap *elf);

int main(int argc, char *argv[]) {
    if(argc < 2) {
        printUsage(argv[0]);
        return -1;
    }

    if(!SettingsParser().parseEnvVar("EGALITO_DEBUG")) {
        printUsage(argv[0]);
        return -2;
    }
    GroupRegistry::getInstance()->dumpSettings();

    LOG(0, "loading ELF program [" << argv[1] << "]");

    //Signals::registerHandlers();

    try {
        ElfMap *elf = new ElfMap(argv[1]);
        ElfMap *interpreter = nullptr;
        if(elf->hasInterpreter()) {
            interpreter = new ElfMap(elf->getInterpreter());
        }

        // set base addresses and map PT_LOAD sections into memory
        const address_t baseAddress = elf->isSharedLibrary() ? 0x4000000 : 0;
        const address_t interpreterAddress = interpreter && interpreter->isSharedLibrary()
            ? 0x7000000 : 0;
        elf->setBaseAddress(baseAddress);
        SegMap::mapSegments(*elf, elf->getBaseAddress());
        if(interpreter) {
            interpreter->setBaseAddress(interpreterAddress);
            SegMap::mapSegments(*interpreter, interpreter->getBaseAddress());
        }

        runEgalito(elf);
        if(interpreter) {
            //examineElf(interpreter);
            //setBreakpointsInInterpreter(interpreter);
        }

        // find entry point
        if(interpreter) {
            entry = interpreter->getEntryPoint() + interpreterAddress;
        }
        else {
            entry = elf->getEntryPoint() + baseAddress;
        }
        CLOG(0, "jumping to entry point at 0x%lx", entry);

        // set up execution environment
        adjustAuxiliaryVector(argv, elf, interpreter);

        // jump to the interpreter/target program (never returns)
        std::cout.flush();
        std::fflush(stdout);
        _start2();
    }
    catch(const char *s) {
        LOG(0, "ERROR: " << s);
        std::cerr << "Error: " << s;
        if(*s && s[std::strlen(s) - 1] != '\n') std::cerr << '\n';
        return 1;
    }

    return 0;
}

void runEgalito(ElfMap *elf) {
    Conductor conductor;
    conductor.parseRecursive(elf);
    //conductor.parse(elf, nullptr);

    auto libc = conductor.getLibraryList()->getLibc();
    if(false && libc) {
        ChunkDumper dumper;
        libc->getElfSpace()->getModule()->accept(&dumper);
    }
    if(false && libc) {
        auto module = libc->getElfSpace()->getModule();
        auto f = module->getChildren()->getNamed()->find("printf_positional");
        JumpTableSearch jt;
        jt.search(module);

        auto tableList = jt.getTableList();
        for(auto table : tableList) {
            std::cout << "found jump table in ["
                << table->getFunction()->getSymbol()->getName() << "] at "
                << std::hex << table->getAddress() << " with "
                << std::dec << table->getEntries()
                << " entries.\n";
        }
    }

    auto module = conductor.getMainSpace()->getModule();
    ChunkDumper dumper;
    module->accept(&dumper);

    auto f = module->getChildren()->getNamed()->find("main");
    if(f) {
        ControlFlowGraph cfg(f);
        cfg.dump();

        JumpTableSearch jt;
        jt.search(f);
    }

    // map shared libraries into memory
    {
        int i = 0;
        for(auto lib : *conductor.getLibraryList()) {
            auto libElfMap = lib->getElfMap();
            if(!libElfMap->isSharedLibrary()) continue;

            const address_t baseAddress = 0xa0000000 + i*0x1000000;
            libElfMap->setBaseAddress(baseAddress);
            SegMap::mapSegments(*libElfMap, libElfMap->getBaseAddress());
            i ++;
        }
    }

    conductor.fixDataSections();

    {
        Generator generator;
        auto sandbox = generator.makeSandbox();
        generator.copyCodeToSandbox(elf, module, sandbox);

        LOG(1, "");
        LOG(1, "=== After copying code to new locations ===");
        ChunkDumper dumper;
        module->accept(&dumper);

        generator.jumpToSandbox(sandbox, module, "_start");
    }
}
