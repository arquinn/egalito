#include <cstring>  // for std::strcmp

extern "C" {
#include <libgen.h>
#include <dirent.h>
}

#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

#include <args.hxx>

#include "conductor/interface.h"
#include "chunk/dump.h"
#include "chunk/library.h"
#include "disasm/disassemble.h"
#include "disasm/handle.h"
#include "disasm/dump.h"
#include "elf/elfmap.h"
#include "instr/writer.h"
#include "operation/mutator.h"


#define D_steamdrill 9
#define JMP_SIZE 5

#include "log/log.h"
#include "log/registry.h"

#include "address.hpp"
#include "tracer_configuration.hpp"
#include "replay_bin_info.hpp"
#include "mem_object.hpp"


// I could do this with the pass api, but not worth it given
// no reuse for this code
using std::function;
using std::initializer_list;
using std::make_pair;
using std::string;
using std::stringstream;
using std::unordered_map;
using std::unique_ptr;
using std::vector;

using Configuration::Address;
using Configuration::RegionIter;
using Configuration::TracerConfiguration;
using Configuration::InstConfiguration;

bool debug;
#define VERBOSE(x) if (debug) {std::cerr << x;}

#define GET_BYTE(x, shift) static_cast<u_char>(((x) >> (shift*8)) & 0xff)
#define GET_BYTES(x, sep) GET_BYTE((x),0) sep GET_BYTE((x),1) sep GET_BYTE((x),2) sep GET_BYTE((x),3)

#define TBEGIN 0x1
#define TEND 0x2

class fxnPointer {
    uintptr_t nextFxn;
    unordered_map<string, uintptr_t> index;
    unordered_map<uintptr_t, string> fxns;

    static unique_ptr<fxnPointer> theInstance;

  public:
    static fxnPointer *getInstance(void) {
        if (theInstance == nullptr) {
            theInstance = unique_ptr<fxnPointer>(new fxnPointer());
            theInstance->index.emplace("tracerBegin", TBEGIN);
            theInstance->index.emplace("tracerEnd", TEND);
            theInstance->fxns.emplace(TBEGIN,"tracerBegin");
            theInstance->fxns.emplace(TEND, "tracerEnd");

            theInstance->nextFxn = TEND + 1;
        }
        return theInstance.get();
    }

    uintptr_t getBegin(void) {return TBEGIN;}
    uintptr_t getEnd(void) {return TEND;}
    uintptr_t getIndex(string input) {
        auto it = index.find(input);
        if (it == index.end()) {
            uintptr_t fxnLoc = nextFxn++;
            it = index.emplace(input, fxnLoc).first;
            fxns.emplace(fxnLoc, input);
        }
        return it->second;
    }

    std::string getFxn(uintptr_t index) {
        auto it = fxns.find(index);
        assert (it != fxns.end());
        return it->second;
    }
};
unique_ptr<fxnPointer> fxnPointer::theInstance = nullptr;

class ElfObj {
  public:
    ElfMap *map;
    vector<ElfSection*> sections;
    uint64_t vaoffset;
    unordered_map<uintptr_t, string> thunks; // I think this seems right?
    SymbolList *funcs;

    ElfObj(std::string s, uintptr_t start, uintptr_t offset ) {
        map = new ElfMap(s.c_str());
        vaoffset = map->isSharedLibrary() ? start - (offset * 0x1000) : 0;
        sections = map->getSectionList();

        // then determine which function it belongs to
        funcs = SymbolList::buildSymbolList(map);
        if (funcs == nullptr) {
            funcs = SymbolList::buildDynamicSymbolList(map); //hmm...?
        }
        std::remove_if(funcs->begin(), funcs->end(),
                       [](Symbol *s) {return !s || s->getType() != Symbol::TYPE_FUNC;});
        std::sort(funcs->begin(), funcs->end(),
                  [](Symbol *x, Symbol *y){return x->getAddress() < y->getAddress();});

        auto thunk = funcs->begin(), end = funcs->end();
        for (; thunk != end; ++thunk) {
            if (strstr((*thunk)->getName(), "get_pc_thunk")) {
                if (strstr((*thunk)->getName(), "get_pc_thunk.bx")) {
                    thunks.emplace((*thunk)->getAddress(), "ebx");
                }
            }
        }
    }

    vector<ElfSection*>::iterator getSections(uintptr_t low, uintptr_t high) {
        return std::find_if(sections.begin(), sections.end(),[low, high] (ElfSection *s) {
                return s->getVirtualAddress() >= low && s->getVirtualAddress() >= high;});
    }
};
unordered_map<string, ElfObj*> elfs;
ElfObj* getElf(string s, uintptr_t start, uintptr_t offset ) {
    auto it = elfs.find(s);
    if (it == elfs.end()) {
        it = elfs.emplace(s, new ElfObj(s,start,offset)).first;
    }
    return it->second;
}


//forward decls
Function* getFunction(address_t lowPC, address_t highPC, ElfObj *elf);

class SteamdrillSO {
  private:
    vector<std::string> pushInsts, popInsts;
    std::string outputFile;
    std::string cfTramp;
    vector<InstConfiguration*> instructionMapping;
    std::unordered_set<string> tracerIsoBlocks;

    vector<string> buildInstBlock(uintptr_t origEip, string outputFxn, string filterFxn);

    static inline string buildLabel(string lname);
  public:
    vector<string> vars;
    vector<string> insts;

    SteamdrillSO(string filename);

    void instrument(Function *toInst, string outputFxn, string filterFxn,
                    string sharedObj, address_t lowAddr, address_t highaddr, const unordered_map<uintptr_t, string>);
    void write(string outFile, string as);
};

string SteamdrillSO::buildLabel(string lname) {
    stringstream label;
    label << ".global " << lname << "\n" << lname << ":\n";
    return label.str();
}


SteamdrillSO::SteamdrillSO(string filename) {
    outputFile = filename;
    pushInsts = { "\tpusha", "\tpushf"};
    popInsts = {"\tpopf", "\tpopa"};

    cfTramp = "cfJmpTramp";
    stringstream tramp;
    tramp << buildLabel(cfTramp) << "\tjmp *cfPtr\n";
    insts.push_back(tramp.str());
}

vector<string> SteamdrillSO::buildInstBlock(uintptr_t origEip, string tracer, string filterFxn) {
    std::vector<std::string> instrs;
    std::stringstream key;
    char eipInst[128];

    key << tracer << "ISO" << filterFxn;
    auto pair = tracerIsoBlocks.insert(key.str());
    if (pair.second) {

        // build a tracerIsolationBlocks for this tracer + filterFxn combio
        assert(!pushInsts.empty() && !popInsts.empty());
        stringstream isoBlkInstrs, tracerEndLabel;
        auto label = buildLabel(key.str());
        tracerEndLabel << "te" << key.str();

        isoBlkInstrs << label;
        for (auto inst : pushInsts) isoBlkInstrs << inst << "\n";
        isoBlkInstrs << "\tcall tracerBegin\n";
        if (!filterFxn.empty()) {
            isoBlkInstrs << "\tcall " << filterFxn + "\n";
            isoBlkInstrs << "\ttestl %eax, %eax\n";
            isoBlkInstrs << "\tjz " << tracerEndLabel.str() <<  "\n";
            isoBlkInstrs << "\tcall " << tracer << "\n";
            isoBlkInstrs << tracerEndLabel.str() << ":\n";
        }
        else {
            isoBlkInstrs << "\tcall " + tracer + "\n";
        }
        isoBlkInstrs << "\tcall tracerEnd\n";
        for (auto inst : popInsts) isoBlkInstrs << inst << "\n";

        isoBlkInstrs << "\tret\n";
        this->insts.push_back(isoBlkInstrs.str());
    }

    // now build the instrumentation for just this guy:
    instrs.push_back("\tmov %esp, (tempEsp)");
    instrs.push_back("\tmov tracerStack, %esp");
    sprintf(eipInst, "\tmovl $0x%x, (origEip)", origEip);
    instrs.push_back(eipInst);
    instrs.push_back("\tcall " + key.str());
    instrs.push_back("\tmov tempEsp, %esp");

    return instrs;
}

inline bool isJmp(int opId) {
    return (opId >= X86_INS_JAE && opId <= X86_INS_JS) || opId == X86_INS_LJMP;
}

inline bool isCondJmp(int opId) {
    return opId >= X86_INS_JAE && opId <= X86_INS_JS && opId != X86_INS_JMP;
}


/*
  auto lstInst = foo->getChildren()->getIterable()->getLast()
  ->getChildren()->getIterable()->getLast();
  address_t jumpTo = lstInst->getAddress() + lstInst->getSize();
  VERBOSE("jumpTo " << jumpTo << std::endl);
  //foo->accept(&dump);
  */


// should really accept tuples of, <low_addr,highAddr, outputFxn, filterFxn>
static int posOpt = 0;
void SteamdrillSO::instrument(Function *func,
                              string outputFxn, string filterFxn,  string sharedObj,
                              address_t lowAddr, address_t highAddr, const unordered_map<uintptr_t, string> thunks) {
    stringstream fxn;
    bool instr = false;
    address_t jmpLoc = 0;

    // this basic structure won't work if we need to have multiple tps at the same address
    for (auto blkIter : CIter::children(func)) {
        auto blkPos = blkIter->getPosition()->get();
        // are we done with blocks?
        if (blkPos > highAddr) {
            jmpLoc = blkPos;
            goto out;
        }

        // determine if this block should be instrumented
        instr = instr || (blkPos <= lowAddr && blkPos + blkIter->getSize() > lowAddr);
        if (instr) {
            bool useJump = blkIter->getSize() >= JMP_SIZE;
            if (useJump) {
                stringstream label;
                label << std::hex << "link" << blkIter->getAddress();
                InstConfiguration *ic = new InstConfiguration;
                ic->setJump(useJump);
                ic->setLink(label.str());
                ic->setSharedObject(sharedObj);
                ic->setBreakpoint(new Address("", "", blkIter->getAddress(), 0)); // pid is unused
                instructionMapping.push_back(ic);
                fxn << buildLabel(label.str());
            }

            for (auto i : CIter::children(blkIter)) {
                Assembly *assem = i->getSemantic()->getAssembly().get();
                // control flow instructions should be considered for two cases:
                // (1) correctness: do they jump to something relative (?)
                // (2) performance: do they jump inside region (?) [ignoring]

                stringstream assemblyInst;
                if (assem->getId() == X86_INS_CALL || assem->getId() == X86_INS_LCALL || isJmp(assem->getId())) {
                    // std::cerr << "worrysome instruction!!" << std::endl;

                    auto asmOps = assem->getAsmOperands();
                    assert (asmOps->getOpCount() == 1);
                    if (asmOps->getOperands()[0].type == X86_OP_IMM) {
                        auto dest = asmOps->getOperands()[0].imm;
                        if (dest >= lowAddr && dest < highAddr)
                            posOpt++;

                        uintptr_t addr = stoi(assem->getOpStr(), NULL, 16);
                        auto thunkIt = thunks.find(addr);
                        if (thunkIt != thunks.end()) {
                            // we need to replace this methinks:
                            assemblyInst << std::hex << "\tmovl $0x" << i->getAddress() + i->getSize()
                                         << ", %" << thunkIt->second << "\n";
                            //assert (false);
                        }
                        else {
                            // we put the destination into cfPtr so that we can call/jump.
                            // note, direct jumps must be relative (or to a label), which
                            // we cannot produce in this case.
                            assemblyInst << "\tmovl $" << assem->getOpStr() << ", (cfPtr)\n";

                            // there is no indirect conditional branches, so use a trampolene
                            if (isCondJmp(assem->getId())) {
                                assemblyInst << "\t" << assem->getMnemonic() << " " << cfTramp << "\n";
                            }
                            // call instructions can leak, so patch them as push+jmp
                            else if (assem->getId() == X86_INS_CALL || assem->getId() == X86_INS_LCALL) {
                                // return address is instruction locaiton + instruction length
                                assemblyInst << "\tpush $0x" << std::hex << i->getAddress() + i->getSize() << "\n";
                                assemblyInst << "\tjmp " << cfTramp << "\n";
                            }
                            // everything else is good as gravy
                            else {
                                assemblyInst << "\t" << assem->getMnemonic() << " *cfPtr\n";
                            }
                        }
                    }
                    else {
                        // we can just allow reg & mem indirect jumps as is... pretty please?
                        assemblyInst << "\t" << assem->getMnemonic() << " " << assem->getOpStr() << "\n";
                    }
                }
                else {
                    assemblyInst << "\t" << assem->getMnemonic() << " " << assem->getOpStr() << "\n";
                }

                if (i->getAddress() >= lowAddr && i->getAddress() < highAddr) {
                    auto toCall = buildInstBlock(i->getAddress(), outputFxn, filterFxn);
                    std::copy(std::begin(toCall), std::end(toCall), std::ostream_iterator<std::string>(fxn, "\n"));
                }
                fxn << assemblyInst.str();
            }
        }
    }

out:
    // We know that a 'jump' instruction point cannot cross a block boundary, so we don't need
    // to do anything special or different here. Except, we need to determine where we should jump to
    //
    // final instruction
    char jmpToInst[64];
    sprintf(jmpToInst, "\tmovl $0x%x, (instEnd)\n", jmpLoc);
    fxn << jmpToInst;
    fxn << std::hex <<"\tjmp *instEnd\n";

    VERBOSE("the instrumented:  " << fxn.str() << std::endl);
    insts.push_back(fxn.str());
}

void SteamdrillSO::write(string ipoints, string as) {
    // egalito.generate(outFile, false);

    std::ofstream out(as);
    //out << "asm(\".data\\n\"";
    out << ".data\n";
    for (auto str : vars)
        out << str;
    //out << ");\n";

    for (auto str : insts) {
        //out << "asm(\".text\\n\"" << str << ");\n";
        out << ".text\n" << str << "\n";
    }

    writeInstPoints(instructionMapping, ipoints);
}

Function* getFunction(address_t lowPC, address_t highPC, ElfObj *elf) {
    // bit kluncy at the end there

    //
    address_t lowVA = lowPC - elf->vaoffset, highVA = highPC - elf->vaoffset;
    auto sec = elf->getSections(lowVA, highVA);
    auto funcs = elf->funcs;

    // figure out what function this belongs to:
    auto sym = funcs->begin(), symEnd = funcs->end();
    for (;sym < symEnd && (*sym)->getAddress() <= lowVA; ++sym);

    auto nxtSym = sym;
    --sym;

    address_t funcStart = (*sym)->getAddress(),
            funcEnd = nxtSym == symEnd ?
            (*sec)->getVirtualAddress() + (*sec)->getSize() : (*nxtSym)->getAddress();


    PositionFactory *positionFactory = PositionFactory::getInstance();
    DisasmHandle handle(true);
    Function *foo = new Function(lowPC);
    foo->setPosition(positionFactory->makeAbsolutePosition(lowPC));

    address_t readAddress = (*sec)->getReadAddress() + (*sec)->convertVAToOffset(lowVA);


    size_t readSize = funcEnd - funcStart + 1;
    cs_insn *insn;
    size_t count = cs_disasm(handle.raw(),
                             (const uint8_t *) readAddress, readSize,
                             lowPC, 0, &insn);

    Block *block = nullptr;
    bool split = true;

    // iterate through all instructions:
    for (size_t j = 0; j < count; ++j) {
        auto ins = &insn[j];
        split = split || cs_insn_group(handle.raw(), ins, X86_INS_ENDBR32);
        if (split) {
            if (block) {
                ChunkMutator(foo, false).append(block);
            }
            Block *nblock = new Block();
            nblock->setPosition(
                positionFactory->makePosition(block, nblock, foo->getSize()));
            block = nblock;
        }
        // check if this instruction ends the current basic block
        // note: technically, Call instructions do not end groups.
        // but, our instrumentation needs it to break a BB... because call's
        // can otherwise leak some instrumentation state:
        split = cs_insn_group(handle.raw(), ins, X86_GRP_JUMP) ||
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

int main(int argc, char *argv[]) {

    args::ArgumentParser parser("Instrument for steamdril.", "ARQ");
    args::Group group(parser, "Required Arguments", args::Group::Validators::All);

    args::Flag verbose(parser, "verbose", "log stuff", {'v', "verbose"});
    args::Positional<string> replay(group, "replay", "the replay for this query");
    args::Positional<string> tracers(group, "tracers", "shared object of tracers");
    args::Positional<string> tpoints(group, "tracepoints", "tracepoints");
    args::Positional<string> ipoints(group, "instpoints", "where to place the instrumentation points");
    args::Positional<string> as(group, "asout", "where to place the assembly");

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

    debug = args::get(verbose);

    auto tps = Configuration::parseTPoints(args::get(tpoints));

    SteamdrillSO instrTPs(args::get(tracers));
    if (args::get(verbose)) {
        auto reg = GroupRegistry::getInstance();
        for (auto name : reg->getSettingNames()) {
            reg->applySetting(name, 11);
        }
    }

    // need logic to combine potentially multiple regions and potentially multiple
    // TracerConfigurations.
    ReplayBinInfo rbi(args::get(replay));
    for (auto tp : tps) {
        if (tp->getOutputFunction() != "UNUSED") {
            tp->forEachBreakpoint(
                [&instrTPs, &rbi](const RegionIter r, const TracerConfiguration &tp) {

                    ChunkDumper dump(true);
                    std::stringstream bpName;
                    bpName << std::hex << tp.getOutputFunction() << "-" << r.first->getOffset();
                    VERBOSE("building instr for " << bpName.str() << std::endl);

                    auto mapping = rbi.getFile(r.first->getOffset());
                    assert (mapping != rbi.files.end());

                    VERBOSE(std::hex << "found mapping " << mapping->name << " "
                            << mapping->start << "-" << mapping->end << std::endl);
                    auto elf = getElf(mapping->name, mapping->start, mapping->offset);

                    auto foo  = getFunction(r.first->getOffset(), r.second->getOffset(), elf);
                    assert (foo);

                    foo->setName(bpName.str());
                    VERBOSE(std::hex << "bp [" << r.first->getOffset() << "-" << r.second->getOffset()
                            << "] in " << r.first->getLibrary() << std::endl);

                    string outputFxn = tp.getOutputFunction(), filterFxn = "";
                    if (tp.getFilter()) {
                        filterFxn = tp.getFilter()->getOutputFunction();
                    }

                    instrTPs.instrument(foo, outputFxn, filterFxn, tp.getSOFile(),
                                        r.first->getOffset(), r.second->getOffset(), elf->thunks);
                });
        }
    }
    instrTPs.write(args::get(ipoints), args::get(as));

    std::cerr << "posible optimizations? " << posOpt << std::endl;
    return 0;
}
