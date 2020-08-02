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
            ic->setBreakpoint(new Address("", "", i->getAddress(), 0)); // pid is unused
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
    // I should fixup how ElfMap works here in order to use endbr instructions

    auto elf = new ElfMap(file.c_str());
    auto sectionVector = elf->getSectionList();

    bool isBP = highPC == lowPC + 1;

    for (auto it : sectionVector) {
        VERBOSE("looking at section " << it->getName()
                << " " << it->getVirtualAddress() << " " << it->getSize() << std::endl );
        if (lowPC >= it->getVirtualAddress() &&
            highPC <= it->getVirtualAddress() + it->getSize())  {

            VERBOSE("in the rigt section" << std::endl);

            PositionFactory *positionFactory = PositionFactory::getInstance();
            DisasmHandle handle(true);
            Function *foo = new Function(lowPC);
            foo->setPosition(positionFactory->makeAbsolutePosition(lowPC));

            // I don't think this always works (?)
            address_t readAddress = it->getReadAddress() + it->convertVAToOffset(lowPC);

            size_t readSize = highPC - lowPC;
            if (isBP) readSize = 20; //the max size of an instruction???

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
    args::Positional<string> replay(group, "replay", "the replay for this query");
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

    ReplayBinInfo rbi(args::get(replay));
    for (auto tp : tps) {
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

                auto foo = getInstRegion(r.first->getOffset(), r.second->getOffset(), mapping->name);
                assert (foo);
                
                foo->setName(bpName.str());
                VERBOSE(std::hex << "bp [" << r.first->getOffset() << "-" << r.second->getOffset()
                        << "] in " << r.first->getLibrary() << std::endl);

                auto lstInst = foo->getChildren()->getIterable()->getLast()
                        ->getChildren()->getIterable()->getLast();
                address_t jumpTo = lstInst->getAddress() + lstInst->getSize();
                VERBOSE("jumpTo " << jumpTo << std::endl);
                //foo->accept(&dump);

                string outputFxn = tp.getOutputFunction(), filterFxn = "";
                if (tp.getFilter()) {
                    filterFxn = tp.getFilter()->getOutputFunction();
                }

                instrTPs.instrument(foo, jumpTo, outputFxn, filterFxn, tp.getSOFile(),
                                    r.first->getOffset(), r.second->getOffset());
            });
    }
    instrTPs.write(args::get(ipoints));

    std::cerr << "posible optimizations? " << posOpt << std::endl;
    return 0;
}
