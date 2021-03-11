#include <cstring>  // for std::strcmp

extern "C" {
#include <libgen.h>
#include <dirent.h>
}

#include <fstream>
#include <functional>
#include <iostream>
#include <list>
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
using std::list;
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

class InstCall {
  public:
    std::string outputFxn, filterFxn, soFile;
    uintptr_t lowAddr, highAddr;
};


class FunctionInst;
class SteamdrillSO {
  private:
    vector<std::string> pushInsts, popInsts;
    std::ofstream assemb;

    std::string cfTramp;
    vector<InstConfiguration*> instructionMapping;
    std::unordered_set<string> tracerIsoBlocks;

    vector<string> buildInstBlock(uintptr_t origEip, list<InstCall> activeCalls);

    static inline string buildLabel(string lname);
  public:
    //vector<string> vars;
    //vector<string> insts;

    SteamdrillSO(string filename);
    ~SteamdrillSO();

    void instrument(unique_ptr<FunctionInst>&);
        //Function* toInst, string outputFxn, string filterFxn,
        //string sharedObj, address_t lowAddr, address_t highaddr, const unordered_map<uintptr_t, string>);
    void writeIPoints(string instPoints);
    string addInstConfiguration(uintptr_t address, bool useJump);
};


class FunctionInst {
  public:
    unique_ptr<Function> function;
    ElfObj *elf;
    map<uintptr_t, InstCall> instRegions;
    u_long lowAddr, highAddr;

    bool contains(uintptr_t addr) { return addr >= lowAddr && addr <= highAddr;}
    void addIR(InstCall tc) { instRegions.emplace(tc.lowAddr, tc);  }
};


//forward decls
unique_ptr<FunctionInst> getFunction(address_t lowPC, address_t highPC, ElfObj *elf);

string SteamdrillSO::buildLabel(string lname) {
    stringstream label;
    label << ".global " << lname << "\n" << lname << ":\n";
    return label.str();
}


SteamdrillSO::SteamdrillSO(string assemblyFile) {
    pushInsts = { "\tpusha", "\tpushf"};
    popInsts = {"\tpopf", "\tpopa"};
    assemb.open(assemblyFile);
    assemb << ".text\n";

    cfTramp = "cfJmpTramp";
    stringstream tramp;
    tramp << buildLabel(cfTramp) << "\tjmp *cfPtr\n";
    assemb << tramp.str() << "\n";
}

SteamdrillSO::~SteamdrillSO() {
    assemb.close(); // make sure this is flushed out when we donzo
}


vector<string> SteamdrillSO::buildInstBlock(uintptr_t origEip, list<InstCall> activeCalls) {
    std::vector<std::string> instrs;
    std::stringstream key;
    char eipInst[128];

    for (auto ac : activeCalls)
        key << ac.outputFxn << "ISO" << ac.filterFxn;

    auto pair = tracerIsoBlocks.insert(key.str());
    if (pair.second) {

        // build a tracerIsolationBlocks for this collection of activeCalls:

        assert(!pushInsts.empty() && !popInsts.empty());
        uintptr_t next = 0;
        stringstream isoBlkInstrs, nextLabel;
        auto label = buildLabel(key.str());
        nextLabel << "te" << key.str();

        isoBlkInstrs << label;
        for (auto inst : pushInsts) isoBlkInstrs << inst << "\n";
        isoBlkInstrs << "\tcall tracerBegin\n";
        for (auto ac : activeCalls) {

            if (!ac.filterFxn.empty()) {
                string endLabel = nextLabel.str() + to_string(next++);

                isoBlkInstrs << "\tcall " << ac.filterFxn + "\n";
                isoBlkInstrs << "\ttestl %eax, %eax\n";
                isoBlkInstrs << "\tjz " << endLabel <<  "\n";
                isoBlkInstrs << "\tcall " << ac.outputFxn << "\n";
                isoBlkInstrs << endLabel << ":\n";
            }
            else {
                isoBlkInstrs << "\tcall " + ac.outputFxn + "\n";
            }
        }

        isoBlkInstrs << "\tcall tracerEnd\n";
        for (auto inst : popInsts) isoBlkInstrs << inst << "\n";

        isoBlkInstrs << "\tret\n";
        assemb << isoBlkInstrs.str() << "\n";
        // this->insts.push_back(isoBlkInstrs.str());
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

std::string SteamdrillSO::addInstConfiguration(uintptr_t address, bool useJump) {
    stringstream label;
    label << std::hex << "link" << address;
    InstConfiguration *ic = new InstConfiguration;
    ic->setJump(useJump);
    ic->setLink(label.str());
    ic->setBreakpoint(new Address("", "", address, 0)); // pid is unused
    instructionMapping.push_back(ic);

    //assert (label.str() != "link804c95b");
    return buildLabel(label.str());
}

void SteamdrillSO::instrument(unique_ptr<FunctionInst> &fi) {
    // do nothing
    std::list<InstCall> activeCalls;

    auto irIter = fi->instRegions.begin(), irEnd = fi->instRegions.end();

    for (auto blkIter : CIter::children(fi->function.get())) {
        auto blkPos = blkIter->getPosition()->get();

        // first update irIter and activeCalls:
        auto acIter = activeCalls.begin(), acEnd = activeCalls.end();
        while (acIter != acEnd) {
            if (blkPos >= acIter->highAddr) {
                acIter = activeCalls.erase(acIter);
            }
            else {
                ++acIter;
            }
        }
        std::cerr << "next inst at " << irIter->second.lowAddr << " " << irIter->second.highAddr << std::endl;;
        for (; irIter != irEnd && blkPos >= irIter->second.highAddr; ++irIter) {}

        // will we need to instrument this next block?
        bool instr = !activeCalls.empty() ||
                (irIter != irEnd && irIter->second.lowAddr >= blkPos && irIter->second.lowAddr <= blkPos + blkIter->getSize());

        // we're done if we (1) not actively instrumenting and (2) done instrumenting
        if (activeCalls.empty() && irIter == irEnd) {
            std::cerr << "done instrumenting "
                      << fi->lowAddr << ", " << fi->highAddr << " at "
                      << blkPos << std::endl;

            return;
        }
        else if (instr) {
            stringstream fxn;
            bool useJump = blkIter->getSize() >= JMP_SIZE;
            if (useJump) {
                string label =  addInstConfiguration(blkIter->getAddress(), useJump);
                fxn << label;
            }
            // mo warnings -> mo problems
            //else {
                //cerr << "cannot use a jump for block " << std::hex << blkPos << "-" <<
                //blkPos + blkIter->getSize() << std::endl;
                    //}
            for (auto i : CIter::children(blkIter)) {
                Assembly *assem = i->getSemantic()->getAssembly().get();
                // control flow instructions should be considered for two cases:
                // (1) correctness: do they jump to something relative (?)
                // (2) performance: do they jump inside region (?) [ignoring]

                stringstream assemblyInst;
                if (assem->getId() == X86_INS_CALL || assem->getId() == X86_INS_LCALL || isJmp(assem->getId())) {
                    auto asmOps = assem->getAsmOperands();
                    assert (asmOps->getOpCount() == 1);
                    if (asmOps->getOperands()[0].type == X86_OP_IMM) {
                        //auto dest = asmOps->getOperands()[0].imm;
                        //if (dest >=  && dest < highAddr)
                        //posOpt++; it's actualy very difficult to calculate this.

                        //uintptr_t addr;
                        //try {
                        //addr = stoul(assem->getOpStr(), NULL, 16);
                        //} catch (std::out_of_range) {
                        //std::cerr << "oops, tried to stoi " << assem->getOpStr() << std::endl;
                        //std::cerr << "assembly address: " << i->getAddress() << std::endl;
                        //assert (false);
                        //}
                        // we shouldn't need this thunk thing because we fix the stack by changing
                        // call instructions now.
                        //auto thunkIt = fi->elf->thunks.find(addr);
                        //if (thunkIt != fi->elf->thunks.end()) {
                        //// we need to replace this methinks:
                        //assemblyInst << std::hex << "\tmovl $0x" << i->getAddress() + i->getSize()
                        //<< ", %" << thunkIt->second << "\n";
                            //assert (false);
                        //}
                        //else {
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
                            // we're removing a cal instruction, tell the library that for the counters:
                            assemblyInst << "\taddl $1, (extraCalls)\n";
                            // return address is instruction locaiton + instruction length
                            assemblyInst << "\tpush $0x" << std::hex << i->getAddress() + i->getSize() << "\n";
                            assemblyInst << "\tjmp " << cfTramp << "\n";
                        }
                        // everything else is good as gravy
                        else {
                            assemblyInst << "\t" << assem->getMnemonic() << " *cfPtr\n";
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

                auto acIter = activeCalls.begin(), acEnd = activeCalls.end();
                while (acIter != acEnd) {
                    if (i->getAddress() >= acIter->highAddr) {
                        acIter = activeCalls.erase(acIter);
                    }
                    else {
                        ++acIter;
                    }
                }

                // update activeCalls for any newly minted things
                for (; irIter != irEnd && i->getAddress() >= irIter->second.lowAddr; ++irIter) {
                    activeCalls.push_back(irIter->second);
                }

                if (!activeCalls.empty()) {
                    if (!useJump) {
                        string label = addInstConfiguration(i->getAddress(), useJump);
                        fxn << label;
                    }

                    auto toCall = buildInstBlock(i->getAddress(), activeCalls);
                    std::copy(std::begin(toCall), std::end(toCall), std::ostream_iterator<std::string>(fxn, "\n"));
                }
                fxn << assemblyInst.str();
            }
            // now add a jump for this block to head to non-instrumentation land:
            char jmpToInst[64];
            sprintf(jmpToInst, "\tmovl $0x%x, (instEnd)\n", blkPos + blkIter->getSize());
            fxn << jmpToInst;
            fxn << std::hex <<"\tjmp *instEnd\n";
            VERBOSE("the instrumented:  " << fxn.str() << std::endl);
            assemb << fxn.str() << "\n";
        }
    }
}

void SteamdrillSO::writeIPoints(string ipoints) {
    writeInstPoints(instructionMapping, ipoints);
}



unique_ptr<FunctionInst> getFunction(address_t lowPC, address_t highPC, ElfObj *elf) {
    // bit kluncy at the end there

    address_t lowVA = lowPC - elf->vaoffset, highVA = highPC - elf->vaoffset;
    auto sec = elf->getSections(lowVA, highVA);
    auto funcs = elf->funcs;

    // figure out what function we're trying to build:
    auto sym = funcs->begin(), symEnd = funcs->end();
    for (;sym < symEnd && (*sym)->getAddress() <= lowVA; ++sym);

    auto nxtSym = sym;
    --sym;

    address_t funcStartVA = (*sym)->getAddress(),
            funcEndVA = nxtSym == symEnd ?
            (*sec)->getVirtualAddress() + (*sec)->getSize() : (*nxtSym)->getAddress();

    address_t funcStart = funcStartVA + elf->vaoffset,
            funcEnd = funcEndVA + elf->vaoffset;


    VERBOSE("within function: " << (*sym)->getName() << 
            " [" << std::hex << funcStartVA << ", " << funcEndVA << ")" << std::endl);
    
    PositionFactory *positionFactory = PositionFactory::getInstance();
    DisasmHandle handle(true);
    ChunkDumper dump(true);
    auto foo = std::make_unique<Function>(funcStart);
    auto fi = std::make_unique<FunctionInst>();
    foo->setPosition(positionFactory->makeAbsolutePosition(funcStart));

    address_t readAddress = (*sec)->getReadAddress() + (*sec)->convertVAToOffset(funcStartVA);

    size_t readSize = funcEndVA - funcStartVA + 1;
    cs_insn *insn;
    size_t count = cs_disasm(handle.raw(),
                             (const uint8_t *) readAddress, readSize,
                             funcStart, 0, &insn);

    // the only way to actually get the blocks is to iterate twice... unless
    // egalito secretly supports 'splitting' blocks? not worth finding out I don't think:
    unordered_set<uint64_t> blockStarts;
    std::cerr << std::hex;
    blockStarts.insert(insn[0].address);
    for (size_t j = 1; j < count; ++j) {
        auto ins = &insn[j];
        if (cs_insn_group(handle.raw(), ins, X86_INS_ENDBR32)) {
            // this is a landing pad for indirect CF
            blockStarts.insert(ins->address);
            //std::cerr << "add block b/c endbr " << ins->address << std::endl;
        }
        else if ( //cs_insn_group(handle.raw(), ins, X86_GRP_RET) ||
                  cs_insn_group(handle.raw(), ins, X86_GRP_CALL)) {
            // the next instruction after a call starts a block for us
            // note: this isn't *actually* true, but our instrumenter relies on it
            blockStarts.insert(ins->address + ins->size);
            //std::cerr << "add block b/c call " << ins->address + ins->size << std::endl;
        }
        else if (cs_insn_group(handle.raw(), ins, X86_GRP_JUMP)) {
            // we look to understand the target of the jump.
            // note: if the target is indirect, then the ENDBR32 better take care of it for us
            auto details = ins->detail->x86;
            assert (details.op_count == 1);
            if (details.operands[0].type == X86_OP_IMM) {
                uintptr_t addr = details.operands[0].imm;
                blockStarts.insert(addr);
                //std::cerr << "add block b/c dest " << addr << std::endl;
            }
            // the next instruction after a jump is a new block (blocks are single exit)
            blockStarts.insert(ins->address + ins->size);
            //std::cerr << "add block b/c jmp " << ins->address + ins->size << std::endl;
        }
    }
    //for (auto bs : blockStarts) {
    //std::cerr << "\block at " << std::hex << bs << std::endl;
    //}

    //assert (false);

    Block *block = nullptr;
    auto bsEnd = blockStarts.end();
    // iterate through all instructions:
    for (size_t j = 0; j < count; ++j) {
        auto ins = &insn[j];
        if (blockStarts.find(ins->address) != bsEnd) {
            if (block) {
                ChunkMutator(foo.get(), false).append(block);
            }
            Block *nblock = new Block();
            nblock->setPosition(
                positionFactory->makePosition(block, nblock, foo->getSize()));
            block = nblock;
        }
        auto instr = Disassemble::instruction(ins, handle, true);
        Chunk *prevChunk = nullptr;
        if(block->getChildren()->getIterable()->getCount() > 0) {
            prevChunk = block->getChildren()->getIterable()->getLast();
        }

        instr->setPosition(
            positionFactory->makePosition(prevChunk, instr, block->getSize()));

        ChunkMutator(block, false).append(instr);
    }

    //foo->accept(&dump);
    if (!block) {
        std::cerr << "something looks seriously wrong "
                  << lowPC << ", " << highPC << std::endl;
        std::cerr << "va addrs: " << lowVA << ", " << highVA << std::endl;
        std::cerr << "read stuffs " << readAddress << " " << readSize << std::endl;
        assert (false);
    }
    if(block->getSize() == 0) {
        delete block;
    }
    else if (block->getSize() > 0) {
        ChunkMutator(foo.get(), false).append(block);
    }
    cs_free(insn, count);

    fi->function = std::move(foo);
    fi->lowAddr = funcStart;
    fi->highAddr = funcEnd;
    fi->elf = elf;
    return fi;
}

int main(int argc, char *argv[]) {

    args::ArgumentParser parser("Instrument for steamdril.", "ARQ");
    args::Group group(parser, "Required Arguments", args::Group::Validators::All);

    args::Flag verbose(parser, "verbose", "log stuff", {'v', "verbose"});
    args::Positional<string> replay(group, "replay", "the replay for this query");
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

    SteamdrillSO instrTPs(args::get(as));
    /*    if (args::get(verbose)) {
        auto reg = GroupRegistry::getInstance();
        for (auto name : reg->getSettingNames()) {
            reg->applySetting(name, 11);
        }
        }*/

    // need logic to combine potentially multiple regions and potentially multiple
    // TracerConfigurations.
    map<uintptr_t, InstCall> instRegions;
    ReplayBinInfo rbi(args::get(replay));
    // duplicates and orders the instrumentation that we need to accomplish:
    for (auto tp : tps) {
        if (tp->getOutputFunction() != "UNUSED") {
            tp->forEachBreakpoint(
                [&instrTPs, &rbi, &instRegions](const RegionIter r, const TracerConfiguration &tp) {
                    InstCall ic;
                    ic.outputFxn = tp.getOutputFunction();
                    ic.filterFxn = tp.getFilter() != nullptr ? tp.getFilter()->getOutputFunction() : "";
                    ic.lowAddr = r.first->getOffset();
                    ic.highAddr = r.second->getOffset();
                    instRegions.emplace(r.first->getOffset(), ic);
                });
        }
    }

    // now split the instRegions into chunks based on what function they're analyzing:
    std::vector<unique_ptr<FunctionInst>> funcs;

    for (auto &irPair : instRegions) {
        // this assumes all tp regions are contained in a single symbol range
        if (funcs.begin() == funcs.end() || !funcs.back()->contains(irPair.first)) {
            auto mapping = rbi.getFile(irPair.first);
            assert (mapping != rbi.files.end());
            VERBOSE("mapping " << mapping->name << " at " << mapping->start << " " << mapping->offset << std::endl;);
            auto elf = getElf(mapping->name, mapping->start, mapping->offset);
            funcs.push_back(getFunction(irPair.second.lowAddr, irPair.second.highAddr,  elf));
        }
        funcs.back()->addIR(irPair.second);
    }

    // now instrument each region:
    for (auto &func : funcs) {
        instrTPs.instrument(func);
    }

    /*
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
                    auto elf = getElf(mapping->name, mapping->start, mapping->offset);

                    VERBOSE(std::hex << "found mapping " << mapping->name << " "
                            << mapping->start << "-" << mapping->end << std::endl);


                    auto foo  = getFunction(r.first->getOffset(), r.second->getOffset(), elf);
                    assert (foo);

                    foo->setName(bpName.str());
                    VERBOSE(std::hex << "bp [" << r.first->getOffset() << "-" << r.second->getOffset()
                            << "] in " << r.first->getLibrary() << std::endl);

                    string outputFxn = tp.getOutputFunction(), filterFxn = "";
                    if (tp.getFilter()) {
                        filterFxn = tp.getFilter()->getOutputFunction();
                    }

                    instrTPs.instrument(foo.get(), outputFxn, filterFxn, tp.getSOFile(),
                                        r.first->getOffset(), r.second->getOffset(), elf->thunks);
                });
        }
    */
    //assert (false);
    instrTPs.writeIPoints(args::get(ipoints));
    //std::cerr << "posible optimizations? " << posOpt << std::endl;

    return 0;
}
