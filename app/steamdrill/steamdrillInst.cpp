#include <cstring>  // for std::strcmp
#include <fstream>
#include <functional>

#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

#include <args.hxx>

#include "conductor/interface.h"
#include "chunk/dump.h"
#include "disasm/disassemble.h"
#include "disasm/handle.h"
#include "elf/elfmap.h"
#include "operation/mutator.h"

// I could do this with the pass api, but not worth it given
// no reuse for this code
using std::string;
using std::unordered_map;
using std::function;

void fixupJumps(Function *f)
{
    // unclear how we get back to the correct instruction?
}

Block *buildInstBlock(Module *m, Function *toCall) {
    // pusha
    // switch stack?
    // tracerBegin      (ptrace_syscall_begin, pauseCounter)
    // tracer
    // tracerEnd (ptrace_syscall_end, startCounter)
    // popa

    Function *begin, *end;
    unordered_map<string, function<void(Function*)>> functions =
            {
                {"tracerBegin", [&begin](Function *f) {begin = f;}},
                {"tracerEnd", [&end](Function *f) {end = f;}}
            };

    for (auto foo : CIter::children(m->getFunctionList())) {
        auto match = functions.find(foo->getName());
        if (match != functions.end())
        {
            match->second(foo);
        }
    }

    assert (begin && "cannot find tracerBegin");
    assert (end && "cannot find tracerEnd");


    return nullptr;
}

void instrument(Function *toInst, Function *toCall)
{
    // Instrumentation block should be:

}


std::pair<uintptr_t, uintptr_t> parseRegions(std::string filename) {
    std::fstream f(filename, std::fstream::in);
    u_long low, high;

    f >> std::hex;
    f >> low;
    f >> high;
    return std::make_pair(low, high);
}

Function* getInstRegion(std::pair<address_t, address_t> &pair, std::string file) {
    auto elf = new ElfMap(file.c_str());
    auto sectionVector = elf->getSectionList();
    std::vector<Block*> blocks;

    for (auto it : sectionVector) {
        if (pair.first >= it->getVirtualAddress() &&
            pair.second <= it->getVirtualAddress() + it->getSize())  {
            std::cout << "The important section is " << it->getName() << std::endl;

            PositionFactory *positionFactory = PositionFactory::getInstance();
            DisasmHandle handle(true);
            ChunkDumper dump;
            Function *foo = new Function(pair.first);
            foo->setPosition(positionFactory->makeAbsolutePosition(pair.first));

            // I don't think this always works (?)
            address_t readAddress = it->getReadAddress() + it->convertVAToOffset(pair.first);
            size_t readSize = pair.second - pair.first;

            cs_insn *insn;
            size_t count = cs_disasm(handle.raw(),
                                     (const uint8_t *) readAddress, readSize,
                                     pair.first, 0, &insn);

            Block *block = new Block();
            block->setPosition(
                positionFactory->makePosition(nullptr, block, foo->getSize()));
            blocks.push_back(block);

            for(size_t j = 0; j < count; j++) {
                auto ins = &insn[j];
                // check if this instruction ends the current basic block
                bool split = cs_insn_group(handle.raw(), ins, X86_GRP_JUMP) ||
                        cs_insn_group(handle.raw(), ins, X86_GRP_CALL) ||
                        cs_insn_group(handle.raw(), ins, X86_GRP_RET);


                auto instr = Disassemble::instruction(ins, handle, true);
                Chunk *prevChunk = nullptr;
                if(block->getChildren()->getIterable()->getCount() > 0) {
                    prevChunk = block->getChildren()->getIterable()->getLast();
                }

                instr->setPosition(
                    positionFactory->makePosition(prevChunk, instr, block->getSize()));

                ChunkMutator(block, false).append(instr);
                if(split) {
                    ChunkMutator(foo, false).append(block);
                    Block *nblock = new Block();
                    nblock->setPosition(
                        positionFactory->makePosition(block, nblock, foo->getSize()));
                    block = nblock;
                }
            }

            if(block->getSize() == 0) {
                delete block;
            }
            else if (block->getSize() > 0) {
                ChunkMutator(foo, false).append(block);
            }

            cs_free(insn, count);
            return foo;
        }
    }
    return nullptr;
}



int main(int argc, char *argv[]) {

    args::ArgumentParser parser("Instrument for steamdril.", "ARQ");
    args::Group group(parser, "Required Arguments", args::Group::Validators::All);

    args::Flag verbose(parser, "verbose", "log stuff", {'v', "verbose"});
    args::Positional<std::string> regions(group, "regions", "The Regions");
    args::Positional<std::string> binary(group, "binary", "The Binary to instrument");
    args::Positional<std::string> tracers(group, "tracers", "The Output");

    try {
        parser.ParseCLI(argc, argv);
    }
    catch (args::Help) {
        std::cerr << parser;
        return 0;
    }
    catch (args::ParseError e) {
        std::cerr << e.what() << std::endl;
        std::cerr << parser;
        return -1;
    }
    catch (args::ValidationError e) {
        std::cerr << e.what() << std::endl;
        std::cerr << parser;
        return -1;
    }

    auto p = parseRegions(args::get(regions));
    auto foo = getInstRegion(p, args::get(binary));
    ChunkDumper dump;
    foo->accept(&dump);

    EgalitoInterface egalito(true, true);
    Module *m = nullptr;

    // Parsing ELF files can throw exceptions.
    egalito.initializeParsing();  // Creates Conductor and Program

    std::cout << "Parsing ELF file\n";
    m = egalito.parse(args::get(tracers), false);
    m->getFunctionList()->getChildren()->add(foo);

    buildInstBlock(m, foo); // fixup foo cannot be called!

    egalito.generate(args::get(tracers) + "_updated");
    return 0;
}
