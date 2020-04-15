#include <cstring>  // for std::strcmp
#include <libgen.h>

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

#include "log/log.h"
#include "log/registry.h"

#include "address.hpp"
#include "tracer_configuration.hpp"

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


//forward decls
Function* getInstRegion(address_t lowPC, address_t highPC, std::string file);

class SteamdrillSO {
  private:
    vector<std::string> pushInsts, popInsts;
    std::string outputFile;
    std::string cfTramp;
    vector<InstConfiguration*> instructionMapping;

    vector<string> buildInstBlock(uintptr_t origEip, string outputFxn, string filterFxn);

    static inline string buildLabel(string lname);
  public:
    vector<string> vars;
    vector<string> insts;

    SteamdrillSO(string filename);

    void instrument(Function *toInst, address_t jmpTo, string outputFxn, string filterFxn,
                    string sharedObj, address_t lowAddr, address_t highaddr);
    void write(string outFile);

    string addFilterVar(string filterName);
};

string SteamdrillSO::buildLabel(string lname) {
    stringstream label;
    label << "\".global " << lname << "\\n\"\n\"" << lname << ":\\n\"\n";
    return label.str();
}

string SteamdrillSO::addFilterVar(string filterName) {
    stringstream newVar;
    newVar << "\t\"" << filterName << "stat:\\n\""
            << "\t\".long 0\\n\"";
    vars.push_back(newVar.str());
    return newVar.str();
}

SteamdrillSO::SteamdrillSO(string filename) {
    outputFile = filename;
    pushInsts = {"\t\"mov %esp, (tempEsp)\\n\"",
                 "\t\"mov tracerStack, %esp\\n\"",
                 "\t\"pusha\\n\"",
                 "\t\"pushf\\n\""};
    popInsts = {"\t\"popf\\n\"",
                "\t\"popa\\n\"",
                "\t\"mov tempEsp, %esp\\n\""};

    cfTramp = "cfJmpTramp";
    stringstream tramp;
    tramp << buildLabel(cfTramp) << "\t\"jmp *cfPtr\\n\"";
    insts.push_back(tramp.str());
}
/*
void SteamdrillSO::initStandardInstBlock(string tracerSO) {
    // auto map = new ElfMap(tracerSO.c_str());
    // auto space = new ElfSpace(map, tracerSO.c_str(), tracerSO.c_str());
    // space->findSymbolsAndRelocs();

    // need to build this ourselves:
    for (auto s : *space->getSymbolList()) {
        vector<Instruction*> *vec = nullptr;
        if (!strncmp(s->getName(), "tracer_push_registers", sizeof("tracer_push_registers"))) {
            vec = &pushInsts;
        }
        else if (!strncmp(s->getName(), "tracer_pop_registers", sizeof("tracer_pop_registers"))) {
            vec = &popInsts;
        }
        if (vec) {
            Function *fxn = getInstRegion(s->getAddress(),
                                          s->getAddress() + 0x1000,
                                          space->getFullPath());
            auto blk = *(CIter::children(fxn).begin());
            for (auto inst : CIter::children(blk)) {
                auto semantic = inst->getSemantic();
                if (semantic->getAssembly()->getMnemonic() == "retl")
                    break;

                vec->push_back(inst);
            }
        }
    }
    free (map);
    free (space);
}

Link *SteamdrillSO::addVariable(string name) {
    if (!targets) {
        createDataSection();
    }
    auto region = static_cast<DataRegion *>(targets->getParent());
    auto offset = targets->getSize();

    auto var = new GlobalVariable(name);
    var->setPosition(new AbsolutePosition(targets->getAddress()+targets->getSize()));

    char *symname = new char[var->getName().length() + 1];
    std::strcpy(symname, var->getName().c_str());

    auto nsymbol = new Symbol(var->getAddress(), 4, symname,
                              Symbol::TYPE_OBJECT, Symbol::BIND_LOCAL, 0, 0); //do these params matter?
    var->setSymbol(nsymbol);

    targets->addGlobalVariable(var);

    targets->setSize(targets->getSize() + 4);
    region->setSize(region->getSize() + 4);

    std::cout << "var " << var->getName() << " @ " << var->getAddress()
              << " " << " link will be..? " << offset << " from " << targets->getName()
              << std::endl;

    return new DataOffsetLink(targets, offset, Link::SCOPE_INTERNAL_DATA);
}


#define DATA_REGION_ADDRESS 0x10000000
#define DATA_REGION_NAME ("region-" #DATA_REGION_ADDRESS)
#define DATA_SECTION_NAME ".ttargets"

// #define DATA_NAMEREGION_ADDRESS 0x11000000
// #define DATA_NAMEREGION_NAME ".ttargets.names"

void SteamdrillSO::createDataSection() {
    auto regionList = module->getDataRegionList();
    auto region = new DataRegion(DATA_REGION_ADDRESS);
    region->setPosition(new AbsolutePosition(DATA_REGION_ADDRESS));
    regionList->getChildren()->add(region);
    region->setParent(regionList);

    targets = new DataSection();
    targets->setName(DATA_SECTION_NAME);
    targets->setAlignment(0x8);
    targets->setPermissions(SHF_WRITE | SHF_ALLOC);
    targets->setPosition(new AbsoluteOffsetPosition(targets, 0));
    targets->setType(DataSection::TYPE_DATA);
    region->getChildren()->add(targets);
    targets->setParent(region);

    auto nameRegion = new DataRegion(DATA_NAMEREGION_ADDRESS);
    nameRegion->setPosition(new AbsolutePosition(DATA_NAMEREGION_ADDRESS));
    regionList->getChildren()->add(nameRegion);
    nameRegion->setParent(regionList);

    names = new DataSection();
    names->setName(DATA_NAMEREGION_NAME);
    names->setAlignment(0x1);
    names->setPermissions(SHF_ALLOC);
    names->setPosition(new AbsoluteOffsetPosition(names, 0));
    names->setType(DataSection::TYPE_DATA);
    namesRegion->getChildren()->add(names);
    names->setParent(nameRegion);
}
*/

vector<string> SteamdrillSO::buildInstBlock(uintptr_t origEip, string tracer, string filterFxn) {
    std::vector<std::string> instrs;
    char eipInst[64];

    assert(!pushInsts.empty() && !popInsts.empty());

    sprintf(eipInst, "\t\"movl $0x%x, (origEip)\\n\"", origEip);

    // how do I add an external link???
    instrs.insert(std::begin(instrs), std::begin(pushInsts), std::end(pushInsts));
    instrs.push_back(eipInst);
    instrs.push_back("\t\"call tracerBegin\\n\"");
    if (!filterFxn.empty()) {
        stringstream tracerEndLabel;
        tracerEndLabel << "te" << std::hex << origEip;

        instrs.push_back("\t\"call " + filterFxn + "\\n\"");
        instrs.push_back("\t\"testl %eax, %eax\\n\"");
        instrs.push_back("\t\"jz " + tracerEndLabel.str()+ "\\n\"");
        instrs.push_back("\t\"call " + tracer + "\\n\"");
        instrs.push_back("\"" + tracerEndLabel.str() + ":\\n\"");
    }
    else {
        instrs.push_back("\t\"call " + tracer + "\\n\"");
    }
    instrs.push_back("\t\"call tracerEnd\\n\"");
    instrs.insert(std::end(instrs), std::begin(popInsts), std::end(popInsts));
    return instrs;

    /*
    auto call = new Instruction();
    auto callSem = new ControlFlowInstruction(X86_INS_CALL, call, "\xff\x1d", "call", 4);
    callSem->setLink(begin);
    call->setSemantic(callSem);
    instrs.push_back(call);

    call = new Instruction();
    callSem = new ControlFlowInstruction(X86_INS_CALL, call, "\xff\x1d", "call", 4);
    callSem->setLink(tlink);
    call->setSemantic(callSem);
    instrs.push_back(call);

    call = new Instruction();
    callSem = new ControlFlowInstruction(X86_INS_CALL, call, "\xff\x1d", "call", 4);
    callSem->setLink(end);
    call->setSemantic(callSem);
    instrs.push_back(call);

    // building this shit from scratch
        // create some relocs... hopefully??
    // create the external symbol?
    auto dynSym = module->getElfSpace()->getDynamicSymbolList();
    size_t offset = dynSym->getCount();
    Symbol *symbol = new Symbol(0, 0, "tracerBegin",
                                Symbol::TYPE_FUNC, Symbol::BIND_GLOBAL,
                                offset, 0);
    dynSym->add(symbol, offset);


    auto relocList = module->getElfSpace()->getRelocList();
    auto section = relocList->getSection(".rel.dyn");
    assert(section);

    auto reloc = new Reloc(begin->getTargetAddress(), R_386_PC32, offset, symbol, 0);
    if(!relocList->add(reloc)) {
    }
    else {
        section->add(reloc);
        }*/
    /*
    DisasmHandle handle(true);
    auto fp = fxnPointer::getInstance();

    vector<u_char> bytes = {0xff, 0x1d, GET_BYTES(fp->getBegin())};
    auto before = DisassembleInstruction(handle).instruction(bytes);
    instrs.push_back(before);

    bytes = {0xff, 0x1d, GET_BYTES(fp->getIndex(tracer))};
    auto call = DisassembleInstruction(handle).instruction(bytes);
    instrs.push_back(call);

    bytes = {0xff, 0x1d, GET_BYTES(fp->getEnd())};
    auto after = DisassembleInstruction(handle).instruction(bytes);
    instrs.push_back(after);
    instrs.insert(std::end(instrs), std::begin(popInsts), std::end(popInsts));
    return instrs;
    */

    // add relocations for each of these... hopefully?

}

inline bool isJmp(int opId) {
    return (opId >= X86_INS_JAE && opId <= X86_INS_JS) || opId == X86_INS_LJMP;
}

inline bool isCondJmp(int opId) {
    return opId >= X86_INS_JAE && opId <= X86_INS_JS && opId != X86_INS_JMP;
}

static int posOpt = 0;
void SteamdrillSO::instrument(Function *toInst, address_t jmpTo,
                              string outputFxn, string filterFxn,  string sharedObj,
                              address_t lowAddr, address_t highAddr) {
    stringstream fxn;
    /*
      string filterVar = ""
    if (!filterFxn.empty()) {
        fitlerVar = addFilterVar(filterFxn);
    }
    */
    for (auto blkIter : CIter::children(toInst)) {
        auto b = blkIter->getChildren()->getIterable();
        for (size_t index = 0; index < b->getCount(); ++index) {
            Instruction *i = b->get(index);
            Assembly *assem = i->getSemantic()->getAssembly().get();

            // control flow instructions should be considered for two cases:
            // (1) correctness: do they jump to something relative (?)
            // (2) performance: do they jump inside region (?) [ignoring]

            stringstream assemblyInst;
            if (assem->getId() == X86_INS_CALL || assem->getId() == X86_INS_LCALL || isJmp(assem->getId())) {
                // std::cerr << "worrysome instruction!!" << std::endl;

                auto asmOps = assem->getAsmOperands();
                assert (asmOps->getOpCount() == 1);
                assert (asmOps->getOperands()[0].type == X86_OP_IMM);
                auto dest = asmOps->getOperands()[0].imm;

                if (dest >= lowAddr && dest < highAddr)
                    posOpt++;

                // relative cf needs to become a direct one.. there is NO relative cf in 32bit
                assemblyInst << "\t\"movl $" << assem->getOpStr() << ", (cfPtr)\\n\"\n";
                if (isCondJmp(assem->getId())) {
                    assemblyInst << "\t\"" << assem->getMnemonic() << " " << cfTramp << "\\n\"";
                }
                else {
                    assemblyInst << "\t\"" << assem->getMnemonic() << " *cfPtr\\n\"";
                }
            }
            else {
                assemblyInst << "\t\"" << assem->getMnemonic() << " " << assem->getOpStr() << "\\n\"\n";
            }
            stringstream label;
            label << std::hex << "link" << i->getAddress();

            InstConfiguration *ic = new InstConfiguration;
            ic->setLink(label.str());
            ic->setSharedObject(sharedObj);
            ic->setBreakpoint(new Address("", "", i->getAddress()));
            instructionMapping.push_back(ic);
            fxn << buildLabel(label.str());

            auto toCall = buildInstBlock(i->getAddress(), outputFxn, filterFxn);
            std::copy(std::begin(toCall), std::end(toCall), std::ostream_iterator<std::string>(fxn, "\n"));
            fxn << assemblyInst.str();
        }
    }

    // final instruction
    char jmpToInst[64];

    sprintf(jmpToInst, "\t\"movl $0x%x, (instEnd)\\n\"", jmpTo);
    fxn << jmpToInst << "\n";

    fxn << std::hex <<"\t\"jmp *instEnd\\n\"";

    std::cerr << "the instrumented function looks like: "
              << fxn.str() << std::endl;
    insts.push_back(fxn.str());
}

void SteamdrillSO::write(string outFile) {
    // egalito.generate(outFile, false);

    std::ofstream out(outputFile, std::ios_base::app);
    out << "asm(\".data\\n\"";
    for (auto str : vars)
        out << str;
    out << ");\n";

    for (auto str : insts) {
        out << "asm(\".text\\n\"" << str << ");\n";
    }

    writeInstPoints(instructionMapping, outFile);
}

Function* getInstRegion(address_t lowPC, address_t highPC, std::string file) {
    auto elf = new ElfMap(file.c_str());
    auto sectionVector = elf->getSectionList();

    bool isBP = highPC == lowPC + 1;

    for (auto it : sectionVector) {
        if (lowPC >= it->getVirtualAddress() &&
            highPC <= it->getVirtualAddress() + it->getSize())  {

            PositionFactory *positionFactory = PositionFactory::getInstance();
            DisasmHandle handle(true);
            Function *foo = new Function(lowPC);
            foo->setPosition(positionFactory->makeAbsolutePosition(lowPC));

            // I don't think this always works (?)
            address_t readAddress = it->getReadAddress() + it->convertVAToOffset(lowPC);

            size_t readSize = highPC - lowPC;
            if (isBP) readSize = 6; //the max size of an instruction???

            cs_insn *insn;
            size_t count = cs_disasm(handle.raw(),
                                     (const uint8_t *) readAddress, readSize,
                                     lowPC, 0, &insn);

            Block *block = new Block();
            block->setPosition(
                positionFactory->makePosition(nullptr, block, foo->getSize()));

            size_t j = 0;

            // iterate through all instructions or just 1 if a breakpoint
            while (j < count && (!isBP || j < 1)) {
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
                ++j;
            }

            if(block->getSize() == 0) {
                delete block;
            }
            else if (block->getSize() > 0) {
                ChunkMutator(foo, false).append(block);
            }

            cs_free(insn, count);
            delete elf;
            return foo;
        }
    }
    delete elf;
    return nullptr;
}



int main(int argc, char *argv[]) {

    args::ArgumentParser parser("Instrument for steamdril.", "ARQ");
    args::Group group(parser, "Required Arguments", args::Group::Validators::All);

    args::Flag verbose(parser, "verbose", "log stuff", {'v', "verbose"});
    args::Positional<string> tracers(group, "tracers", "shared object of tracers");
    args::Positional<string> tpoints(group, "tracepoints", "tracepoints");
    args::Positional<string> ipoints(group, "instpoints", "where to place the instrumentation points");

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

    for (auto tp : tps) {
        tp->forEachBreakpoint(
            [&instrTPs](const RegionIter r, const TracerConfiguration &tp) {

                ChunkDumper dump(true);

                std::stringstream bpName;
                bpName << std::hex << tp.getOutputFunction() << "-" << r.first->getOffset();

                auto foo = getInstRegion(r.first->getOffset(),
                                         r.second->getOffset(),
                                         r.first->getLibrary());
                foo->setName(bpName.str());
                VERBOSE(std::hex
                          << "bp [" << r.first->getOffset()
                          << "-"    << r.second->getOffset()
                          << "] in " << r.first->getLibrary()
                          << "found " << foo->getSize()
                        << std::endl);

                auto lstInst = foo->getChildren()->getIterable()->getLast()
                        ->getChildren()->getIterable()->getLast();
                address_t jumpTo = lstInst->getAddress() + lstInst->getSize();
                VERBOSE("jumpTo " << jumpTo << std::endl);
                //foo->accept(&dump);

                string outputFxn = tp.getOutputFunction(), filterFxn = "";
                TracerConfiguration *filter = nullptr;
                if ((filter = tp.getFilter())) {
                    filterFxn = filter->getOutputFunction();
                }

                instrTPs.instrument(foo, jumpTo, outputFxn, filterFxn, tp.getSOFile(),
                                    r.first->getOffset(), r.second->getOffset());
            });
    }
    instrTPs.write(args::get(ipoints));

    std::cerr << "posible optimizations? " << posOpt << std::endl;
    return 0;
}
