#ifndef EGALITO_TYPES_H
#define EGALITO_TYPES_H

#include <cstdint>  // for uint64_t
#include <cstddef>  // for size_t

#if defined(ARCH_ARM) || defined(ARCH_I686)
typedef uint32_t address_t;
typedef int32_t diff_t;
#else
typedef uint64_t address_t;
typedef int64_t diff_t;
#endif
typedef std::size_t size_t;


#endif
