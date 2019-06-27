#ifndef EGALITO_PE_PEMAP_H
#define EGALITO_PE_PEMAP_H

#ifdef USE_WIN64_PE

#include <vector>
#include <string>
#include "types.h"
#include "exefile/exemap.h"

#include "parser-library/parse.h"

class PESection : public ExeSectionImpl {
private:
    peparse::image_section_header header;
    peparse::bounded_buffer *buffer;
    uint32_t characteristics;
public:
    PESection(int index, const std::string &name, address_t baseAddress,
        peparse::image_section_header header, peparse::bounded_buffer *buffer);

    //peparse::bounded_buffer *getBuffer() const { return buffer; }
    const char *getReadPtr() const { return reinterpret_cast<const char *>(buffer->buf); }
    size_t getReadSize() const { return buffer->bufLen; }
    virtual size_t getSize() const { return header.Misc.VirtualSize; }
    size_t getOffset() const { return header.PointerToRawData; }

    bool isReadable() const { return characteristics & peparse::IMAGE_SCN_MEM_READ; }
    bool isWritable() const { return characteristics & peparse::IMAGE_SCN_MEM_WRITE; }
    virtual bool isExecutable() const { return characteristics & peparse::IMAGE_SCN_MEM_EXECUTE; }

    bool isCode() const
        { return characteristics & peparse::IMAGE_SCN_CNT_CODE; }
    bool isData() const
        { return characteristics & peparse::IMAGE_SCN_CNT_INITIALIZED_DATA; }
    bool isBSS() const
        { return characteristics & peparse::IMAGE_SCN_CNT_UNINITIALIZED_DATA; }
    bool isAllocated() const
        { return !(characteristics & peparse::IMAGE_SCN_MEM_DISCARDABLE); }
};

class PEMap : public ExeMapImpl<PESection> {
private:
    peparse::parsed_pe *peRef;
public:
    PEMap(const std::string &filename);
    ~PEMap();

    virtual PEMap *asPE() { return this; }
    virtual peparse::parsed_pe *getPERef() { return peRef; }
    address_t getPEImageBase() { return peRef->peHeader.nt.OptionalHeader64.ImageBase; }

    static bool isPE(const std::string &filename);
private:
    void throwError(const std::string &err);
    void setup();
    void parsePE(const std::string &filename);
    void verifyPE();
    void makeSectionMap();
    void findDataDirectories();
    //void makeSegmentList();
    //void makeVirtualAddresses();
public:
    virtual address_t getEntryPoint() const;
    virtual address_t getSectionAlignment() const;

    PESection *findSectionContaining(address_t address) const;

    template <typename T>
    T getReadAddress(address_t virtualAddress);
};

template <typename T>
T PEMap::getReadAddress(address_t virtualAddress) {
    auto section = findSectionContaining(virtualAddress);
    if(!section) return nullptr;

    return reinterpret_cast<T>(section->getReadAddress()
        + (virtualAddress - section->getVirtualAddress()));
}

#else

class PEMap : public ExeMap {
};

#endif  // USE_WIN64_PE
#endif